// Lean compiler output
// Module: Gen.PrimeGeneration
// Imports: Init Mathlib.Data.Nat.Prime Mathlib.Data.List.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_prime__count___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_sieve__loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_largest__prime__le(lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_largest__prime__le___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples_mark__from(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_get___rarg(lean_object*, lean_object*);
static lean_object* l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1;
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime___boxed(lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_List_setTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_collect(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_sqrt(lean_object*);
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_prime__count(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_replicateTR___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_primes__up__to___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_init__bool__list(lean_object*);
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime(lean_object*);
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime__trial__division(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_nth__prime(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_nth__prime___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_sieve__loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_primes__up__to(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples_mark__from___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime__trial__division___boxed(lean_object*);
static lean_object* _init_l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples_mark__from(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_4, x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_12 = 1;
x_13 = l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1;
x_14 = lean_box(x_12);
lean_inc(x_4);
x_15 = l_List_setTR_go___rarg(x_4, x_14, x_4, x_7, x_13);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples_mark__from___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Gen_PrimeGeneration_mark__multiples_mark__from(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mul(x_1, x_1);
x_5 = l_Gen_PrimeGeneration_mark__multiples_mark__from(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_mark__multiples___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_PrimeGeneration_mark__multiples(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_init__bool__list(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = l_List_replicateTR___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_sieve__loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_nat_mul(x_2, x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_3, x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_List_get___rarg(x_3, x_7);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = l_Gen_PrimeGeneration_mark__multiples(x_2, x_1, x_3);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_sieve__loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_PrimeGeneration_sieve__up__to_sieve__loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_List_lengthTRAux___rarg(x_2, x_6);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_instInhabitedBool;
x_10 = lean_box(x_9);
x_11 = l___private_Init_Util_0__outOfBounds___rarg(x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_3 = x_14;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_3);
x_22 = l_List_get___rarg(x_2, x_3);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_3 = x_25;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_3 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_3);
x_33 = l_List_reverse___rarg(x_4);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Gen_PrimeGeneration_sieve__up__to_collect(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = 0;
x_7 = lean_box(x_6);
lean_inc(x_5);
x_8 = l_List_replicateTR___rarg(x_5, x_7);
x_9 = l_Gen_PrimeGeneration_sieve__up__to_sieve__loop(x_1, x_2, x_8);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Gen_PrimeGeneration_sieve__up__to_collect(x_5, x_9, x_11, x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_sieve__up__to___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_primes__up__to(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_primes__up__to___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_primes__up__to(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_nat_mod(x_1, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = 1;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime__trial__division(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_nat_mod(x_1, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Nat_sqrt(x_1);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Gen_PrimeGeneration_is__prime__trial__division_check__divisors(x_1, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime__trial__division___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Gen_PrimeGeneration_is__prime__trial__division(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Gen_PrimeGeneration_is__prime(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Gen_PrimeGeneration_is__prime__trial__division(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_is__prime___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Gen_PrimeGeneration_is__prime(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_prime__count(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_prime__count___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_prime__count(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_nth__prime(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = lean_nat_mul(x_1, x_5);
lean_dec(x_5);
x_7 = l_Gen_PrimeGeneration_sieve__up__to(x_6);
lean_dec(x_6);
x_8 = l_List_lengthTRAux___rarg(x_7, x_2);
x_9 = lean_nat_dec_le(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_1, x_11);
x_13 = lean_nat_dec_lt(x_12, x_8);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_7);
x_14 = l_instInhabitedNat;
x_15 = l___private_Init_Util_0__outOfBounds___rarg(x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_List_get___rarg(x_7, x_12);
lean_dec(x_7);
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(0u);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_nth__prime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_nth__prime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_largest__prime__le(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
x_3 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_instInhabitedNat;
x_5 = l_List_getLast_x21___rarg(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Gen_PrimeGeneration_largest__prime__le___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_PrimeGeneration_largest__prime__le(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Prime(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_PrimeGeneration(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Prime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1 = _init_l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1();
lean_mark_persistent(l_Gen_PrimeGeneration_mark__multiples_mark__from___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
