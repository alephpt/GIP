// Lean compiler output
// Module: Gen.SymmetryPreservation
// Imports: Init Gen.Symmetry Gen.Projection Gen.Comp
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
LEAN_EXPORT lean_object* l_Gen_SymmetryPreservation_CriticalLine;
static lean_object* _init_l_Gen_SymmetryPreservation_CriticalLine() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Symmetry(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Projection(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Comp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_SymmetryPreservation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Symmetry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Projection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Comp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_SymmetryPreservation_CriticalLine = _init_l_Gen_SymmetryPreservation_CriticalLine();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
