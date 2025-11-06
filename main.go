package main

import (
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand"
	"net"
	"os"
	"strconv"
	"strings"
	"time"
	"unicode"
)

type DNSRecordType uint16

const (
	DNSTypeA     DNSRecordType = 1
	DNSTypeNS    DNSRecordType = 2
	DNSTypeCNAME DNSRecordType = 5
	DNSTypeSOA   DNSRecordType = 6
	DNSTypePTR   DNSRecordType = 12
	DNSTypeMX    DNSRecordType = 15
	DNSTypeTXT   DNSRecordType = 16
	DNSTypeAAAA  DNSRecordType = 28
	DNSTypeSRV   DNSRecordType = 33
	DNSTypeDNAME DNSRecordType = 39
	DNSTypeDS    DNSRecordType = 43
	DNSTypeRRSIG DNSRecordType = 46
	DNSTypeNSEC  DNSRecordType = 47
	DNSTypeDNSKEY DNSRecordType = 48
	DNSTypeHTTPS DNSRecordType = 65
	DNSTypeANY   DNSRecordType = 255
)

type DNSRecord struct {
	Name       string
	Type       DNSRecordType
	TTL        uint32
	Data       interface{}
	Section    string
	Preference *uint16
	RData      []byte
}

type SOAData struct {
	MName   string `json:"mname"`
	RName   string `json:"rname"`
	Serial  uint32 `json:"serial"`
	Refresh uint32 `json:"refresh"`
	Retry   uint32 `json:"retry"`
	Expire  uint32 `json:"expire"`
	Minimum uint32 `json:"minimum"`
}

type SRVData struct {
	Priority uint16 `json:"priority"`
	Weight   uint16 `json:"weight"`
	Port     uint16 `json:"port"`
	Target   string `json:"target"`
}

type DSData struct {
	KeyTag     uint16 `json:"key_tag"`
	Algorithm  uint8  `json:"algorithm"`
	DigestType uint8  `json:"digest_type"`
	Digest     string `json:"digest"`
}

type DNSKEYData struct {
	Flags     uint16 `json:"flags"`
	Protocol  uint8  `json:"protocol"`
	Algorithm uint8  `json:"algorithm"`
	Key       string `json:"key"`
}

type DNSResolver struct {
	DefaultServers []string
	Timeout        time.Duration
	Retries        int
	UseTCP         bool
	ValidateDNSSEC bool
	MaxRedirects   int
	queryStats     map[string]int
}

var dnsTypeMap = map[string]DNSRecordType{
	"A":      DNSTypeA,
	"NS":     DNSTypeNS,
	"CNAME":  DNSTypeCNAME,
	"SOA":    DNSTypeSOA,
	"PTR":    DNSTypePTR,
	"MX":     DNSTypeMX,
	"TXT":    DNSTypeTXT,
	"AAAA":   DNSTypeAAAA,
	"SRV":    DNSTypeSRV,
	"DNAME":  DNSTypeDNAME,
	"DS":     DNSTypeDS,
	"RRSIG":  DNSTypeRRSIG,
	"NSEC":   DNSTypeNSEC,
	"DNSKEY": DNSTypeDNSKEY,
	"HTTPS":  DNSTypeHTTPS,
	"ANY":    DNSTypeANY,
}

func NewDNSResolver() *DNSResolver {
	return &DNSResolver{
		DefaultServers: []string{"8.8.8.8:53", "1.1.1.1:53", "9.9.9.9:53", "208.67.222.222:53"},
		Timeout:        5 * time.Second,
		Retries:        3,
		UseTCP:         false,
		ValidateDNSSEC: false,
		MaxRedirects:   15,
		queryStats:     make(map[string]int),
	}
}

func isValidLabel(label string) bool {
	if len(label) == 0 || len(label) > 63 {
		return false
	}
	
	for i, r := range label {
		if !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '-' && r != '_' {
			return false
		}
		if i == 0 && r == '-' {
			return false
		}
		if i == len(label)-1 && r == '-' {
			return false
		}
	}
	return true
}

func (r *DNSResolver) IsValidDomain(domain string) bool {
	if domain == "" || len(domain) > 253 {
		return false
	}

	labels := strings.Split(domain, ".")
	if len(labels) < 1 {
		return false
	}

	for _, label := range labels {
		if !isValidLabel(label) {
			return false
		}
	}
	return true
}

func (r *DNSResolver) BuildQuery(domain string, queryType DNSRecordType) ([]byte, uint16) {
	if !r.IsValidDomain(domain) {
		panic("Invalid domain name: " + domain)
	}

	tid := uint16(rand.Intn(65536))
	flags := uint16(0x0100)

	header := make([]byte, 12)
	binary.BigEndian.PutUint16(header[0:2], tid)
	binary.BigEndian.PutUint16(header[2:4], flags)
	binary.BigEndian.PutUint16(header[4:6], 1)
	binary.BigEndian.PutUint16(header[6:8], 0)
	binary.BigEndian.PutUint16(header[8:10], 0)
	binary.BigEndian.PutUint16(header[10:12], 1)

	var qname []byte
	for _, label := range strings.Split(domain, ".") {
		qname = append(qname, byte(len(label)))
		qname = append(qname, []byte(label)...)
	}
	qname = append(qname, 0)

	question := make([]byte, 4)
	binary.BigEndian.PutUint16(question[0:2], uint16(queryType))
	binary.BigEndian.PutUint16(question[2:4], 1)

	edns := make([]byte, 11)
	edns[0] = 0
	binary.BigEndian.PutUint16(edns[1:3], 41)
	binary.BigEndian.PutUint16(edns[3:5], 4096)
	if r.ValidateDNSSEC {
		binary.BigEndian.PutUint32(edns[5:9], 0x80000000)
	} else {
		binary.BigEndian.PutUint32(edns[5:9], 0)
	}
	binary.BigEndian.PutUint16(edns[9:11], 0)

	query := append(header, qname...)
	query = append(query, question...)
	query = append(query, edns...)

	return query, tid
}

func (r *DNSResolver) ParseName(data []byte, offset int) (string, int) {
	if offset >= len(data) {
		panic("Offset beyond packet length")
	}

	var labels []string
	jumped := false
	originalOffset := offset
	maxJumps := 20
	jumpCount := 0
	seenPointers := make(map[int]bool)

	for {
		if seenPointers[offset] {
			panic("DNS compression loop detected")
		}
		seenPointers[offset] = true

		if offset >= len(data) {
			panic("DNS packet parsing overflow")
		}

		length := int(data[offset])
		if length == 0 {
			offset++
			break
		}

		if (length & 0xC0) == 0xC0 {
			if offset+1 >= len(data) {
				panic("Invalid DNS pointer offset")
			}
			pointer := int(binary.BigEndian.Uint16(data[offset:offset+2])) & 0x3FFF
			if pointer >= len(data) {
				panic("DNS pointer out of bounds")
			}
			if !jumped {
				originalOffset = offset + 2
			}
			offset = pointer
			jumped = true
			jumpCount++
			if jumpCount > maxJumps {
				panic("Too many DNS pointer jumps")
			}
			continue
		}

		offset++
		if offset+length > len(data) {
			panic("DNS label length exceeds packet size")
		}
		labels = append(labels, string(data[offset:offset+length]))
		offset += length
	}

	if jumped {
		return strings.Join(labels, "."), originalOffset
	}
	return strings.Join(labels, "."), offset
}

func (r *DNSResolver) ParseRecordData(rtype DNSRecordType, rdata []byte, packet []byte, rdataStart int) interface{} {
	defer func() {
		if recover() != nil {
			fmt.Printf("Failed to parse record type %d, returning hex\n", rtype)
		}
	}()

	switch rtype {
	case DNSTypeA:
		if len(rdata) != 4 {
			return hex.EncodeToString(rdata)
		}
		return net.IP(rdata).String()

	case DNSTypeAAAA:
		if len(rdata) != 16 {
			return hex.EncodeToString(rdata)
		}
		return net.IP(rdata).String()

	case DNSTypeMX:
		if len(rdata) < 3 {
			panic("MX record too short")
		}
		preference := binary.BigEndian.Uint16(rdata[:2])
		exchange, _ := r.ParseName(packet, rdataStart+2)
		return map[string]interface{}{
			"exchange":   exchange,
			"preference": preference,
		}

	case DNSTypeSRV:
		if len(rdata) < 7 {
			panic("SRV record too short")
		}
		priority := binary.BigEndian.Uint16(rdata[:2])
		weight := binary.BigEndian.Uint16(rdata[2:4])
		port := binary.BigEndian.Uint16(rdata[4:6])
		target, _ := r.ParseName(packet, rdataStart+6)
		return SRVData{
			Priority: priority,
			Weight:   weight,
			Port:     port,
			Target:   target,
		}

	case DNSTypeCNAME, DNSTypeNS, DNSTypePTR, DNSTypeDNAME:
		name, _ := r.ParseName(packet, rdataStart)
		return name

	case DNSTypeTXT:
		var parts []string
		pos := 0
		for pos < len(rdata) {
			if pos+1 > len(rdata) {
				break
			}
			txtLen := int(rdata[pos])
			pos++
			if pos+txtLen > len(rdata) {
				break
			}
			parts = append(parts, string(rdata[pos:pos+txtLen]))
			pos += txtLen
		}
		return strings.Join(parts, "")

	case DNSTypeSOA:
		offset := rdataStart
		mname, offset := r.ParseName(packet, offset)
		rname, offset := r.ParseName(packet, offset)
		if offset+20 > len(packet) {
			panic("SOA numeric fields truncated")
		}
		serial := binary.BigEndian.Uint32(packet[offset : offset+4])
		refresh := binary.BigEndian.Uint32(packet[offset+4 : offset+8])
		retry := binary.BigEndian.Uint32(packet[offset+8 : offset+12])
		expire := binary.BigEndian.Uint32(packet[offset+12 : offset+16])
		minimum := binary.BigEndian.Uint32(packet[offset+16 : offset+20])
		return SOAData{
			MName:   mname,
			RName:   rname,
			Serial:  serial,
			Refresh: refresh,
			Retry:   retry,
			Expire:  expire,
			Minimum: minimum,
		}

	case DNSTypeDS:
		if len(rdata) < 4 {
			panic("DS record too short")
		}
		keyTag := binary.BigEndian.Uint16(rdata[:2])
		algorithm := rdata[2]
		digestType := rdata[3]
		digest := hex.EncodeToString(rdata[4:])
		return DSData{
			KeyTag:     keyTag,
			Algorithm:  algorithm,
			DigestType: digestType,
			Digest:     digest,
		}

	case DNSTypeDNSKEY:
		if len(rdata) < 4 {
			panic("DNSKEY record too short")
		}
		flags := binary.BigEndian.Uint16(rdata[:2])
		protocol := rdata[2]
		algorithm := rdata[3]
		key := hex.EncodeToString(rdata[4:])
		return DNSKEYData{
			Flags:     flags,
			Protocol:  protocol,
			Algorithm: algorithm,
			Key:       key,
		}

	default:
		return hex.EncodeToString(rdata)
	}
}

func (r *DNSResolver) ParseResponse(data []byte, tid uint16) []DNSRecord {
	if len(data) < 12 {
		panic("DNS response too short")
	}

	respTid := binary.BigEndian.Uint16(data[0:2])
	flags := binary.BigEndian.Uint16(data[2:4])
	qdcount := binary.BigEndian.Uint16(data[4:6])
	ancount := binary.BigEndian.Uint16(data[6:8])
	nscount := binary.BigEndian.Uint16(data[8:10])
	arcount := binary.BigEndian.Uint16(data[10:12])

	if respTid != tid {
		panic("Transaction ID mismatch")
	}
	if (flags>>15)&1 != 1 {
		panic("Not a DNS response")
	}

	totalRRs := int(qdcount) + int(ancount) + int(nscount) + int(arcount)
	if totalRRs > 1000 {
		panic("Excessive RR count")
	}

	rcode := flags & 0xF
	if rcode != 0 {
		errorCodes := map[uint16]string{
			0: "NOERROR", 1: "FORMERR", 2: "SERVFAIL", 3: "NXDOMAIN",
			4: "NOTIMP", 5: "REFUSED", 6: "YXDOMAIN", 7: "YXRRSET",
			8: "NXRRSET", 9: "NOTAUTH", 10: "NOTZONE",
		}
		panic("DNS error: " + errorCodes[rcode])
	}

	truncated := (flags>>9)&1 == 1
	if truncated && !r.UseTCP {
		fmt.Fprintf(os.Stderr, "Warning: Response truncated (TC=1), consider using TCP\n")
	}

	var records []DNSRecord
	offset := 12

	for i := 0; i < int(qdcount); i++ {
		_, offset = r.ParseName(data, offset)
		if offset+4 > len(data) {
			panic("Question section truncated")
		}
		offset += 4
	}

	sections := []struct {
		name  string
		count uint16
	}{
		{"answer", ancount},
		{"authority", nscount},
		{"additional", arcount},
	}

	for _, section := range sections {
		for i := 0; i < int(section.count); i++ {
			name, newOffset := r.ParseName(data, offset)
			offset = newOffset

			if offset+10 > len(data) {
				panic("RR header exceeds packet size")
			}

			rtype := DNSRecordType(binary.BigEndian.Uint16(data[offset : offset+2]))
			rclass := binary.BigEndian.Uint16(data[offset+2 : offset+4])
			ttl := binary.BigEndian.Uint32(data[offset+4 : offset+8])
			rdlength := binary.BigEndian.Uint16(data[offset+8 : offset+10])
			offset += 10

			if offset+int(rdlength) > len(data) {
				panic("RR data exceeds packet size")
			}

			rdata := data[offset : offset+int(rdlength)]
			rdataStart := offset
			offset += int(rdlength)

			if rclass != 1 {
				continue
			}

			parsedData := r.ParseRecordData(rtype, rdata, data, rdataStart)
			record := DNSRecord{
				Name:    name,
				Type:    rtype,
				TTL:     ttl,
				Data:    parsedData,
				Section: section.name,
				RData:   rdata,
			}

			if rtype == DNSTypeMX {
				if mxData, ok := parsedData.(map[string]interface{}); ok {
					preference := mxData["preference"].(uint16)
					record.Preference = &preference
					record.Data = mxData["exchange"]
				}
			}

			records = append(records, record)
		}
	}

	return records
}

func (r *DNSResolver) SendQuery(query []byte, server string) ([]byte, error) {
	if r.UseTCP {
		conn, err := net.DialTimeout("tcp", server, r.Timeout)
		if err != nil {
			return nil, err
		}
		defer conn.Close()
		conn.SetDeadline(time.Now().Add(r.Timeout))

		lengthBuf := make([]byte, 2)
		binary.BigEndian.PutUint16(lengthBuf, uint16(len(query)))
		if _, err := conn.Write(append(lengthBuf, query...)); err != nil {
			return nil, err
		}

		responseLengthBuf := make([]byte, 2)
		if _, err := conn.Read(responseLengthBuf); err != nil {
			return nil, err
		}
		responseLength := binary.BigEndian.Uint16(responseLengthBuf)

		response := make([]byte, responseLength)
		if _, err := conn.Read(response); err != nil {
			return nil, err
		}
		return response, nil
	} else {
		conn, err := net.DialTimeout("udp", server, r.Timeout)
		if err != nil {
			return nil, err
		}
		defer conn.Close()
		conn.SetDeadline(time.Now().Add(r.Timeout))

		if _, err := conn.Write(query); err != nil {
			return nil, err
		}

		response := make([]byte, 4096)
		n, err := conn.Read(response)
		if err != nil {
			return nil, err
		}
		return response[:n], nil
	}
}

func (r *DNSResolver) ProcessRecords(records []DNSRecord, domain string, queryType DNSRecordType, server string, followCnames bool) []DNSRecord {
	if queryType == DNSTypeANY {
		return records
	}

	var targetRecords, cnameRecords []DNSRecord
	for _, rec := range records {
		if rec.Type == queryType && rec.Section == "answer" {
			targetRecords = append(targetRecords, rec)
		}
		if rec.Type == DNSTypeCNAME && rec.Section == "answer" {
			cnameRecords = append(cnameRecords, rec)
		}
	}

	if len(targetRecords) > 0 {
		return targetRecords
	} else if followCnames && len(cnameRecords) > 0 {
		cnameTarget := cnameRecords[0].Data.(string)
		fmt.Fprintf(os.Stderr, "Following CNAME %s -> %s\n", domain, cnameTarget)
		return r.Resolve(cnameTarget, queryType, server, true)
	}

	return nil
}

func (r *DNSResolver) Resolve(domain string, queryType interface{}, server string, followCnames bool) []DNSRecord {
	if !r.IsValidDomain(domain) {
		panic("Invalid domain format: " + domain)
	}

	var qType DNSRecordType
	switch v := queryType.(type) {
	case string:
		var ok bool
		qType, ok = dnsTypeMap[strings.ToUpper(v)]
		if !ok {
			panic("Unsupported query type: " + v)
		}
	case DNSRecordType:
		qType = v
	case []string:
		var results []DNSRecord
		for _, qt := range v {
			results = append(results, r.Resolve(domain, qt, server, followCnames)...)
		}
		return results
	case []DNSRecordType:
		var results []DNSRecord
		for _, qt := range v {
			results = append(results, r.Resolve(domain, qt, server, followCnames)...)
		}
		return results
	default:
		panic("Invalid query type")
	}

	servers := r.DefaultServers
	if server != "" {
		servers = []string{server}
	}

	var lastErrors []string

	for attempt := 0; attempt < r.Retries; attempt++ {
		for _, currentServer := range servers {
			r.queryStats[currentServer]++

			query, tid := r.BuildQuery(domain, qType)
			startTime := time.Now()

			data, err := r.SendQuery(query, currentServer)
			if err != nil {
				lastErrors = append(lastErrors, fmt.Sprintf("%s: %v", currentServer, err))
				continue
			}

			if len(data) == 0 {
				lastErrors = append(lastErrors, fmt.Sprintf("%s: Empty response", currentServer))
				continue
			}

			records := r.ParseResponse(data, tid)
			if len(records) == 0 {
				lastErrors = append(lastErrors, fmt.Sprintf("%s: No records in response", currentServer))
				continue
			}

			finalRecords := r.ProcessRecords(records, domain, qType, currentServer, followCnames)
			if finalRecords != nil {
				fmt.Fprintf(os.Stderr, "Resolved %s (%v) via %s in %v\n", 
					domain, qType, currentServer, time.Since(startTime))
				return finalRecords
			}

			lastErrors = append(lastErrors, fmt.Sprintf("%s: No matching records", currentServer))
		}

		if attempt < r.Retries-1 {
			backoff := time.Duration(1<<uint(attempt)) * time.Second
			if backoff > 10*time.Second {
				backoff = 10 * time.Second
			}
			time.Sleep(backoff)
		}
	}

	panic("All attempts failed. Errors: " + strings.Join(lastErrors, ", "))
}

func (r *DNSResolver) Query(domain string, queryType interface{}, server string, verbose bool, jsonOutput bool, followCnames bool) {
	defer func() {
		if err := recover(); err != nil {
			fmt.Fprintf(os.Stderr, "\nError resolving %s: %v\n\n", domain, err)
		}
	}()

	records := r.Resolve(domain, queryType, server, followCnames)

	if jsonOutput {
		var qtypeStr interface{}
		switch v := queryType.(type) {
		case string:
			qtypeStr = v
		case DNSRecordType:
			for k, val := range dnsTypeMap {
				if val == v {
					qtypeStr = k
					break
				}
			}
		case []string:
			qtypeStr = v
		case []DNSRecordType:
			var types []string
			for _, qt := range v {
				for k, val := range dnsTypeMap {
					if val == qt {
						types = append(types, k)
						break
					}
				}
			}
			qtypeStr = types
		}

		result := map[string]interface{}{
			"domain":    domain,
			"query_type": qtypeStr,
			"records":   records,
		}
		jsonData, _ := json.MarshalIndent(result, "", "  ")
		fmt.Println(string(jsonData))
		return
	}

	var typeStr string
	switch v := queryType.(type) {
	case string:
		typeStr = v
	case DNSRecordType:
		for k, val := range dnsTypeMap {
			if val == v {
				typeStr = k
				break
			}
		}
	case []string:
		typeStr = strings.Join(v, ",")
	case []DNSRecordType:
		var types []string
		for _, qt := range v {
			for k, val := range dnsTypeMap {
				if val == qt {
					types = append(types, k)
					break
				}
			}
		}
		typeStr = strings.Join(types, ",")
	}

	fmt.Printf("\nDNS %s records for %s:\n", typeStr, domain)

	sections := map[string][]DNSRecord{
		"answer":     {},
		"authority":  {},
		"additional": {},
	}

	for _, rec := range records {
		sections[rec.Section] = append(sections[rec.Section], rec)
	}

	for _, secName := range []string{"answer", "authority", "additional"} {
		if len(sections[secName]) > 0 {
			fmt.Printf("\n;; %s Section:\n", strings.Title(secName))
			for _, rec := range sections[secName] {
				if verbose {
					fmt.Printf("%s\t%d\t%v\n", rec.Name, rec.TTL, rec.Data)
				} else {
					fmt.Printf("%v\n", rec.Data)
				}
			}
		}
	}
	fmt.Println()
}

func (r *DNSResolver) GetStats() map[string]int {
	return r.queryStats
}

func validateServerString(serverStr string) string {
	parts := strings.Split(serverStr, ":")
	if len(parts) == 0 || len(parts) > 2 {
		panic("Invalid server format: " + serverStr)
	}

	ip := parts[0]
	port := "53"
	if len(parts) > 1 {
		port = parts[1]
	}

	if net.ParseIP(ip) == nil {
		panic("Invalid IP address: " + ip)
	}

	if p, err := strconv.Atoi(port); err != nil || p <= 0 || p > 65535 {
		panic("Invalid port number: " + port)
	}

	return ip + ":" + port
}

func main() {
	rand.Seed(time.Now().UnixNano())

	var (
		domain        string
		queryType     string
		server        string
		useTCP        bool
		validateDNSSEC bool
		noFollowCnames bool
		verbose       bool
		jsonOutput    bool
		debug         bool
	)

	flag.StringVar(&domain, "domain", "", "Domain name to query")
	flag.StringVar(&queryType, "type", "A", "DNS record type (A, AAAA, MX, etc.) or comma-separated list")
	flag.StringVar(&server, "server", "", "Specific DNS server (ip:port)")
	flag.BoolVar(&useTCP, "tcp", false, "Use TCP instead of UDP")
	flag.BoolVar(&validateDNSSEC, "dnssec", false, "Set DO bit (request DNSSEC records)")
	flag.BoolVar(&noFollowCnames, "no-follow-cnames", false, "Disable following CNAME records")
	flag.BoolVar(&verbose, "verbose", false, "Verbose output")
	flag.BoolVar(&jsonOutput, "json", false, "Output in JSON format")
	flag.BoolVar(&debug, "debug", false, "Enable debug output")

	flag.Parse()

	if domain == "" {
		if len(flag.Args()) > 0 {
			domain = flag.Args()[0]
		} else {
			fmt.Fprintln(os.Stderr, "Error: Domain name is required")
			os.Exit(1)
		}
	}

	defer func() {
		if err := recover(); err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
	}()

	var validatedServer string
	if server != "" {
		validatedServer = validateServerString(server)
	}

	var queryTypes interface{}
	if strings.Contains(queryType, ",") {
		queryTypes = strings.Split(queryType, ",")
	} else {
		queryTypes = queryType
	}

	resolver := NewDNSResolver()
	resolver.UseTCP = useTCP
	resolver.ValidateDNSSEC = validateDNSSEC

	resolver.Query(domain, queryTypes, validatedServer, verbose, jsonOutput, !noFollowCnames)
}
