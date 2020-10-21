typedef int MyType;

typedef struct {} Empty;

struct Pair {
    int a;
    int b;
};

void swap(MyType* a, int* b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

Pair swapRet(struct Pair* pair) {
}

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
    int myNumber = 2718;
    addNumbers(31415, myNumber);
}

void declsTest() {
    int a, b = 20, c = 33, d, e = 5;
}