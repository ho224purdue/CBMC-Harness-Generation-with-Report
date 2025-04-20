void HTTPClient_AddRangeHeader_harness() {
    HTTPRequestHeaders_t * pRequestHeaders = mallocCanFail(sizeof(HTTPRequestHeaders_t));
    int32_t rangeStartOrlastNbytes = nondet_uint();
    int32_t rangeEnd = nondet_uint();

    __CPROVER_assume(pRequestHeaders != NULL);
    __CPROVER_assume(pRequestHeaders->pBuffer != NULL);
    __CPROVER_assume(rangeEnd >= -1);
    __CPROVER_assume((rangeStartOrlastNbytes >= 0) || (rangeEnd == -1));
    __CPROVER_assume((rangeEnd == -1) || (rangeStartOrlastNbytes <= rangeEnd));
    __CPROVER_assume(rangeStartOrlastNbytes != INT32_MIN);

    HTTPClient_AddRangeHeader(pRequestHeaders, rangeStartOrlastNbytes, rangeEnd);
}
