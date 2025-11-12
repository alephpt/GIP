// Lean compiler output
// Module: Gen.ZetaEvaluation
// Imports: Init Gen.Basic Gen.PrimeGeneration Gen.MonoidalStructure Gen.PartialEulerProducts Gen.EulerProductColimit Mathlib.Data.Nat.Prime
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
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_partial__euler__factor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__S(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_p__adic__val___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_nat__pow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_nat__pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_geometric__sum__lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_partial__euler__factor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__gen___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__gen(lean_object*);
uint8_t l_Gen_PrimeGeneration_is__prime__trial__division(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_geometric__sum__lcm___boxed(lean_object*, lean_object*);
lean_object* l_Gen_PrimeGeneration_sieve__up__to(lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_p__adic__val(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_p__adic__val(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_le(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_nat_mod(x_2, x_1);
x_8 = lean_nat_dec_eq(x_7, x_3);
lean_dec(x_7);
x_9 = l_instDecidableNot___rarg(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_div(x_2, x_1);
x_11 = l_Gen_ZetaEvaluation_p__adic__val(x_1, x_10);
lean_dec(x_10);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(0u);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(0u);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_p__adic__val___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_ZetaEvaluation_p__adic__val(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_nat__pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Gen_ZetaEvaluation_nat__pow(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_mul(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_nat__pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_ZetaEvaluation_nat__pow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_geometric__sum__lcm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Gen_ZetaEvaluation_nat__pow(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_geometric__sum__lcm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_ZetaEvaluation_geometric__sum__lcm(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_partial__euler__factor(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Gen_PrimeGeneration_is__prime__trial__division(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(1u);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Gen_ZetaEvaluation_p__adic__val(x_1, x_2);
x_6 = l_Gen_ZetaEvaluation_geometric__sum__lcm(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_partial__euler__factor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_ZetaEvaluation_partial__euler__factor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Gen_ZetaEvaluation_partial__euler__factor(x_4, x_1);
x_7 = l_Nat_lcm(x_2, x_6);
lean_dec(x_6);
lean_dec(x_2);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__S(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(x_2, x_3, x_1);
lean_dec(x_1);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__gen(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Gen_PrimeGeneration_sieve__up__to(x_1);
x_7 = l_List_foldl___at_Gen_ZetaEvaluation_compute__zeta__S___spec__1(x_1, x_4, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(1u);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Gen_ZetaEvaluation_compute__zeta__gen___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_ZetaEvaluation_compute__zeta__gen(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_PrimeGeneration(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_MonoidalStructure(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_PartialEulerProducts(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_EulerProductColimit(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Prime(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_ZetaEvaluation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_PrimeGeneration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_MonoidalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_PartialEulerProducts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_EulerProductColimit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Prime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
