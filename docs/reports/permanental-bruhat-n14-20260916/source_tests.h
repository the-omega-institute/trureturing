#ifndef PSW_SOURCE_TESTS_H
#define PSW_SOURCE_TESTS_H

/* Literal public expectations, entered before implementation/evaluation.
   Pan thesis pp.50,53; explicit f6 worked example p.53. */
typedef struct {
    const char *name;
    unsigned n;
    unsigned char input[14];
    unsigned char output[14];
} SourceCase;

static const SourceCase source_cases[] = {
    {"f4-1234",4,{1,2,3,4},{1,2,3,4}},
    {"f4-1243",4,{1,2,4,3},{1,4,3,2}},
    {"f4-2134",4,{2,1,3,4},{3,2,1,4}},
    {"f4-2143",4,{2,1,4,3},{3,4,1,2}},
    {"f5-worked",5,{2,1,5,3,4},{5,2,3,4,1}},
    {"f5-append",5,{1,2,4,3,5},{1,4,3,2,5}},
    {"f5-middle",5,{1,2,3,5,4},{1,2,5,4,3}},
    {"f5-nonidentity",5,{2,1,5,4,3},{5,4,3,2,1}},
    {"f5-identity",5,{1,2,3,4,5},{1,2,3,4,5}},
    {"f6-worked",6,{2,3,1,5,6,4},{5,2,3,6,1,4}}
};

static const unsigned char operation_input[14] = {2,1,6,4,3,5};
static const unsigned char insertion_expected[14] = {2,1,7,6,4,3,5};
static const unsigned char swapping_expected[14] = {2,1,7,4,6,5,3};
static const unsigned char ru_expected[14] = {2,4,3,1,6,5};
/* Thesis p.48: RU(216435) = RU via reverse then value complement. */
static const unsigned char append_expected[14] = {2,1,6,4,3,5,7};

/* Thesis p.60 displayed obstruction; the displayed maximum determines slots.
   It is a statement about arbitrary comparable inputs, not recursive f. */
static const unsigned char obstruction_u[14] = {1,2,3,5,6,4};
static const unsigned char obstruction_v[14] = {1,2,3,6,5,4};
static const unsigned char obstruction_ins[14] = {1,2,3,5,6,7,4};
static const unsigned char obstruction_inss[14] = {1,2,3,6,7,4,5};
static const unsigned char obstruction_true_f6[14] = {1,2,5,6,3,4};

/* Tableau-criterion example, thesis p.59; do not copy its misprinted table. */
static const unsigned char order_lower[14] = {2,1,4,3};
static const unsigned char order_upper[14] = {3,2,4,1};

#endif
