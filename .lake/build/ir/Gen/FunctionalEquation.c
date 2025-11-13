// Lean compiler output
// Module: Gen.FunctionalEquation
// Imports: Init Gen.Basic Gen.Comp Mathlib.Analysis.Complex.Basic
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
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* l_Gen_FunctionalEquation_xi__completed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_FunctionalEquation_CriticalLine;
LEAN_EXPORT lean_object* l_Gen_FunctionalEquation_xi__completed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 0;
x_3 = lean_sorry(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Gen_FunctionalEquation_CriticalLine() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Comp(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_FunctionalEquation(uint8_t builtin, lean_object* w) {
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
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_FunctionalEquation_CriticalLine = _init_l_Gen_FunctionalEquation_CriticalLine();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
