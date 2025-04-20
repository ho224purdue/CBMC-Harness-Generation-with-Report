void HTTPClient_ReadHeader_harness() {
    HTTPResponse_t * pResponse = mallocCanFail(sizeof(HTTPResponse_t));
    __CPROVER_assume(pResponse != NULL);

    pResponse->pBuffer = (uint8_t *)mallocCanFail(nondet_uint());
    __CPROVER_assume(pResponse->pBuffer != NULL);

    pResponse->bufferLen = nondet_uint();
    __CPROVER_assume(pResponse->bufferLen > 0);

    const char * pField = (const char *)mallocCanFail(nondet_uint());
    size_t fieldLen = nondet_uint();
    __CPROVER_assume(pField != NULL && fieldLen > 0);

    const char ** pValueLoc = (const char **)mallocCanFail(sizeof(const char *));
    __CPROVER_assume(pValueLoc != NULL);

    size_t * pValueLen = (size_t *)mallocCanFail(sizeof(size_t));
    __CPROVER_assume(pValueLen != NULL);

    HTTPClient_ReadHeader(pResponse, pField, fieldLen, pValueLoc, pValueLen);
}
