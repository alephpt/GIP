// Lean compiler output
// Module: Gen.PartialEulerProducts
// Imports: Init Gen.Basic Gen.Colimit Gen.MonoidalStructure Mathlib.Data.Nat.Prime Mathlib.Data.Finset.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PartialEulerProducts_union__prime__sets(lean_object*, lean_object*);
static lean_object* l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2;
LEAN_EXPORT lean_object* l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_ndunion___at_Gen_PartialEulerProducts_union__prime__sets___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_PartialEulerProducts_empty__prime__set;
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldrTR___at_Gen_PartialEulerProducts_union__prime__sets___spec__3(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Gen_PartialEulerProducts_singleton__prime(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* _init_l_Gen_PartialEulerProducts_empty__prime__set() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Gen_PartialEulerProducts_singleton__prime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2;
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_List_elem___rarg(x_3, x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2(x_8, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_Gen_PartialEulerProducts_union__prime__sets___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = l_List_redLength___rarg(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l_List_toArrayAux___rarg(x_2, x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
return x_1;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4(x_5, x_9, x_10, x_1);
lean_dec(x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Multiset_ndunion___at_Gen_PartialEulerProducts_union__prime__sets___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldrTR___at_Gen_PartialEulerProducts_union__prime__sets___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_PartialEulerProducts_union__prime__sets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldrTR___at_Gen_PartialEulerProducts_union__prime__sets___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Gen_PartialEulerProducts_union__prime__sets___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Colimit(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_MonoidalStructure(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Prime(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_PartialEulerProducts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Colimit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_MonoidalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Prime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_PartialEulerProducts_empty__prime__set = _init_l_Gen_PartialEulerProducts_empty__prime__set();
lean_mark_persistent(l_Gen_PartialEulerProducts_empty__prime__set);
l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1 = _init_l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1();
lean_mark_persistent(l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__1);
l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2 = _init_l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2();
lean_mark_persistent(l_List_insert___at_Gen_PartialEulerProducts_union__prime__sets___spec__2___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
