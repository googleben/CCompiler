int* main(void) {
    int t;
    t = (int)5.0;
    return (int*)(42+5+3);
}

int addNumbers(int numberA, int numberB) {
    return numberA + numberB;
}

void fun() {
    main();
    fun();
    int myNumber;
    myNumber = 2718;
    addNumbers(31415, myNumber);
}
