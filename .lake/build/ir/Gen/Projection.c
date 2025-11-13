// Lean compiler output
// Module: Gen.Projection
// Imports: Init Gen.Basic Gen.Comp Gen.MonoidalStructure Gen.EulerProductColimit Gen.Morphisms Mathlib.CategoryTheory.Category.Basic Mathlib.CategoryTheory.Functor.Basic Mathlib.CategoryTheory.Limits.Shapes.Terminal
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
LEAN_EXPORT lean_object* l_Gen_Projection_gen__comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_gen__id(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__obj(lean_object*);
lean_object* l_Gen_idMorph(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_gen__id___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__obj__N__all;
extern lean_object* l_Gen_Comp_AnalyticFunctionSpace_entire;
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__directed__system(lean_object*, lean_object*);
extern lean_object* l_Gen_Comp_AnalyticFunctionSpace_zeta__domain;
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__directed__system___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_gen__gamma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_GenDirectedSystem_objects___default(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__obj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__obj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_Comp_AnalyticFunctionSpace_entire;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__obj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_Projection_F__R__obj(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_Projection_F__R__obj__N__all() {
_start:
{
lean_object* x_1; 
x_1 = l_Gen_Comp_AnalyticFunctionSpace_zeta__domain;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_gen__id(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_idMorph(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_gen__id___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_Projection_gen__id(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_gen__comp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(7, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_gen__gamma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_GenDirectedSystem_objects___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__directed__system(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_Comp_AnalyticFunctionSpace_entire;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_Projection_F__R__directed__system___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Gen_Projection_F__R__directed__system(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Comp(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_MonoidalStructure(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_EulerProductColimit(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Morphisms(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Category_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Functor_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Limits_Shapes_Terminal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_Projection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Comp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_MonoidalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_EulerProductColimit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Morphisms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Category_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Functor_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Limits_Shapes_Terminal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_Projection_F__R__obj__N__all = _init_l_Gen_Projection_F__R__obj__N__all();
lean_mark_persistent(l_Gen_Projection_F__R__obj__N__all);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
