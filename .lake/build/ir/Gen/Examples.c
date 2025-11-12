// Lean compiler output
// Module: Gen.Examples
// Imports: Init Gen.ZetaEvaluation Gen.PrimeGeneration Gen.MonoidalStructure
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
lean_object* l_Nat_lcm(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_sample__results___closed__6;
static lean_object* l_Gen_Examples_test__suite___closed__16;
static lean_object* l_Gen_Examples_sample__results___closed__4;
static uint8_t l_Gen_Examples_test__suite___closed__2;
static uint8_t l_Gen_Examples_test__suite___closed__5;
uint8_t l_Nat_instDecidableCoprime(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__7;
LEAN_EXPORT uint8_t l_List_foldr___at_Gen_Examples_test__all___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Examples_test__suite;
static lean_object* l_Gen_Examples_tested__values___closed__1;
static lean_object* l_Gen_Examples_test__suite___closed__10;
LEAN_EXPORT uint8_t l_Gen_Examples_check__multiplicativity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Examples_analyze__growth(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_sample__results___closed__5;
static lean_object* l_Gen_Examples_test__suite___closed__3;
lean_object* l_List_range(lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__9;
LEAN_EXPORT lean_object* l_Gen_Examples_count__prime__factors(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Examples_count__prime__factors___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Gen_Examples_test__all___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__12;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__13;
static lean_object* l_Gen_Examples_test__suite___closed__15;
static lean_object* l_Gen_Examples_sample__results___closed__7;
lean_object* l_Gen_ZetaEvaluation_compute__zeta__gen(lean_object*);
static lean_object* l_Gen_Examples_sample__results___closed__1;
static uint8_t l_Gen_Examples_test__suite___closed__11;
LEAN_EXPORT lean_object* l_Gen_Examples_tested__values;
static lean_object* l_Gen_Examples_test__suite___closed__1;
LEAN_EXPORT lean_object* l_Gen_Examples_check__locality___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Examples_check__multiplicativity___boxed(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__6;
LEAN_EXPORT lean_object* l_Gen_Examples_sample__results;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static uint8_t l_Gen_Examples_test__suite___closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Examples_analyze__prime(lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__4;
lean_object* l_Gen_PrimeGeneration_sieve__up__to(lean_object*);
LEAN_EXPORT uint8_t l_Gen_Examples_check__locality(lean_object*);
static lean_object* l_Gen_Examples_test__suite___closed__14;
static lean_object* l_Gen_Examples_sample__results___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Gen_Examples_sample__results___closed__3;
LEAN_EXPORT uint8_t l_Gen_Examples_test__all;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Gen_Examples_sample__results___closed__8;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Gen_Examples_sample__results___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Gen_Examples_check__multiplicativity(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_instDecidableCoprime(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_nat_mul(x_1, x_2);
x_6 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_5);
lean_dec(x_5);
x_7 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
x_8 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_2);
x_9 = l_Nat_lcm(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Gen_Examples_check__multiplicativity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Gen_Examples_check__multiplicativity(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Gen_Examples_check__locality(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
x_3 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(x_1, x_4, x_2);
lean_dec(x_2);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Gen_Examples_check__locality___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Gen_Examples_check__locality(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_Examples_analyze__prime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
x_3 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Gen_Examples_analyze__growth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_div(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Gen_Examples_count__prime__factors(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Gen_Examples_count__prime__factors___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_Examples_count__prime__factors(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
return x_2;
}
}
static uint8_t _init_l_Gen_Examples_test__suite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Gen_Examples_test__suite___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Gen_Examples_test__suite___closed__2;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
return x_2;
}
}
static uint8_t _init_l_Gen_Examples_test__suite___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Gen_Examples_test__suite___closed__4;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Gen_Examples_test__suite___closed__5;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
return x_2;
}
}
static uint8_t _init_l_Gen_Examples_test__suite___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Gen_Examples_test__suite___closed__7;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Gen_Examples_test__suite___closed__8;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
return x_2;
}
}
static uint8_t _init_l_Gen_Examples_test__suite___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Gen_Examples_test__suite___closed__10;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Gen_Examples_test__suite___closed__11;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Gen_Examples_test__suite___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Gen_Examples_test__suite___closed__9;
x_2 = l_Gen_Examples_test__suite___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Gen_Examples_test__suite___closed__6;
x_2 = l_Gen_Examples_test__suite___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Gen_Examples_test__suite___closed__3;
x_2 = l_Gen_Examples_test__suite___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_test__suite() {
_start:
{
lean_object* x_1; 
x_1 = l_Gen_Examples_test__suite___closed__16;
return x_1;
}
}
static lean_object* _init_l_Gen_Examples_tested__values___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_Examples_tested__values() {
_start:
{
lean_object* x_1; 
x_1 = l_Gen_Examples_tested__values___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Gen_Examples_test__all___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Gen_Examples_test__all___spec__1(x_1, x_4);
x_6 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_5;
}
}
}
}
static uint8_t _init_l_Gen_Examples_test__all() {
_start:
{
uint8_t x_1; lean_object* x_2; uint8_t x_3; 
x_1 = 1;
x_2 = l_Gen_Examples_tested__values;
x_3 = l_List_foldr___at_Gen_Examples_test__all___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Gen_Examples_test__all___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Gen_Examples_test__all___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Gen_Examples_sample__results___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(100u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = l_Gen_Examples_sample__results___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = l_Gen_Examples_sample__results___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = l_Gen_Examples_sample__results___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Gen_Examples_sample__results___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_Gen_Examples_sample__results___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Gen_Examples_sample__results___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Gen_Examples_sample__results___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Gen_Examples_sample__results() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Gen_Examples_sample__results___closed__8;
x_3 = l_List_mapTR_loop___at_Gen_Examples_sample__results___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_ZetaEvaluation(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_PrimeGeneration(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_MonoidalStructure(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_Examples(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_ZetaEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_PrimeGeneration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_MonoidalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_Examples_test__suite___closed__1 = _init_l_Gen_Examples_test__suite___closed__1();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__1);
l_Gen_Examples_test__suite___closed__2 = _init_l_Gen_Examples_test__suite___closed__2();
l_Gen_Examples_test__suite___closed__3 = _init_l_Gen_Examples_test__suite___closed__3();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__3);
l_Gen_Examples_test__suite___closed__4 = _init_l_Gen_Examples_test__suite___closed__4();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__4);
l_Gen_Examples_test__suite___closed__5 = _init_l_Gen_Examples_test__suite___closed__5();
l_Gen_Examples_test__suite___closed__6 = _init_l_Gen_Examples_test__suite___closed__6();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__6);
l_Gen_Examples_test__suite___closed__7 = _init_l_Gen_Examples_test__suite___closed__7();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__7);
l_Gen_Examples_test__suite___closed__8 = _init_l_Gen_Examples_test__suite___closed__8();
l_Gen_Examples_test__suite___closed__9 = _init_l_Gen_Examples_test__suite___closed__9();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__9);
l_Gen_Examples_test__suite___closed__10 = _init_l_Gen_Examples_test__suite___closed__10();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__10);
l_Gen_Examples_test__suite___closed__11 = _init_l_Gen_Examples_test__suite___closed__11();
l_Gen_Examples_test__suite___closed__12 = _init_l_Gen_Examples_test__suite___closed__12();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__12);
l_Gen_Examples_test__suite___closed__13 = _init_l_Gen_Examples_test__suite___closed__13();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__13);
l_Gen_Examples_test__suite___closed__14 = _init_l_Gen_Examples_test__suite___closed__14();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__14);
l_Gen_Examples_test__suite___closed__15 = _init_l_Gen_Examples_test__suite___closed__15();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__15);
l_Gen_Examples_test__suite___closed__16 = _init_l_Gen_Examples_test__suite___closed__16();
lean_mark_persistent(l_Gen_Examples_test__suite___closed__16);
l_Gen_Examples_test__suite = _init_l_Gen_Examples_test__suite();
lean_mark_persistent(l_Gen_Examples_test__suite);
l_Gen_Examples_tested__values___closed__1 = _init_l_Gen_Examples_tested__values___closed__1();
lean_mark_persistent(l_Gen_Examples_tested__values___closed__1);
l_Gen_Examples_tested__values = _init_l_Gen_Examples_tested__values();
lean_mark_persistent(l_Gen_Examples_tested__values);
l_Gen_Examples_test__all = _init_l_Gen_Examples_test__all();
l_Gen_Examples_sample__results___closed__1 = _init_l_Gen_Examples_sample__results___closed__1();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__1);
l_Gen_Examples_sample__results___closed__2 = _init_l_Gen_Examples_sample__results___closed__2();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__2);
l_Gen_Examples_sample__results___closed__3 = _init_l_Gen_Examples_sample__results___closed__3();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__3);
l_Gen_Examples_sample__results___closed__4 = _init_l_Gen_Examples_sample__results___closed__4();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__4);
l_Gen_Examples_sample__results___closed__5 = _init_l_Gen_Examples_sample__results___closed__5();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__5);
l_Gen_Examples_sample__results___closed__6 = _init_l_Gen_Examples_sample__results___closed__6();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__6);
l_Gen_Examples_sample__results___closed__7 = _init_l_Gen_Examples_sample__results___closed__7();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__7);
l_Gen_Examples_sample__results___closed__8 = _init_l_Gen_Examples_sample__results___closed__8();
lean_mark_persistent(l_Gen_Examples_sample__results___closed__8);
l_Gen_Examples_sample__results = _init_l_Gen_Examples_sample__results();
lean_mark_persistent(l_Gen_Examples_sample__results);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
