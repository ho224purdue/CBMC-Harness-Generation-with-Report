void HTTPClient_AddHeader_harness() {
    HTTPRequestHeaders_t * pRequestHeaders = mallocCanFail(sizeof(HTTPRequestHeaders_t));
    const char * pField = (const char *)mallocCanFail(nondet_uint());
    size_t fieldLen = nondet_uint();
    const char * pValue = (const char *)mallocCanFail(nondet_uint());
    size_t valueLen = nondet_uint();

    __CPROVER_assume(pRequestHeaders != NULL);
    __CPROVER_assume(pField != NULL);
    __CPROVER_assume(pValue != NULL);
    __CPROVER_assume(fieldLen > 0);
    __CPROVER_assume(valueLen > 0);

    __CPROVER_assume(pRequestHeaders->pBuffer != NULL);
    __CPROVER_assume(pRequestHeaders->headersLen <= pRequestHeaders->bufferLen);

    HTTPClient_AddHeader(pRequestHeaders, pField, fieldLen, pValue, valueLen);
}
