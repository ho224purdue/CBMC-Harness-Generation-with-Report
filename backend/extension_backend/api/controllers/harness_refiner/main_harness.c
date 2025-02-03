void main_harness() {
    unsigned int user_input = nondet_uint();
    __CPROVER_assume(user_input <= 5);

    // Initialize global counter
    unsigned int global_counter = nondet_uint();
    __CPROVER_assume(global_counter >= 0 && global_counter <= 10);

    // Assumptions for stub function returns
    int sensor_val1 = nondet_int();
    int sensor_val2 = nondet_int();
    
    // Loop unwinding assumption
    unsigned int i;
    __CPROVER_assume(i < user_input);

    // Assumptions for result constraints
    int result = nondet_int();
    __CPROVER_assume(result > -1000);

    // Call main function
    int ret = main();

    // Post-conditions
    __CPROVER_assert(ret >= 0, "main return value is non-negative");
    __CPROVER_assert(global_counter >= 0, "global counter remains non-negative");
}