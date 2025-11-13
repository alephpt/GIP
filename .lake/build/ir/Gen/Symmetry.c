// Lean compiler output
// Module: Gen.Symmetry
// Imports: Init Gen.Basic Gen.MonoidalStructure Gen.EulerProductColimit Gen.EquilibriumBalance
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
LEAN_EXPORT lean_object* l_Gen_Symmetry_SymmetryAxis;
LEAN_EXPORT lean_object* l_Gen_Symmetry_BalanceAxis;
static lean_object* _init_l_Gen_Symmetry_SymmetryAxis() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Gen_Symmetry_BalanceAxis() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_MonoidalStructure(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_EulerProductColimit(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_EquilibriumBalance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_Symmetry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_MonoidalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_EulerProductColimit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_EquilibriumBalance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_Symmetry_SymmetryAxis = _init_l_Gen_Symmetry_SymmetryAxis();
l_Gen_Symmetry_BalanceAxis = _init_l_Gen_Symmetry_BalanceAxis();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
