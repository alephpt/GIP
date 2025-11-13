// Lean compiler output
// Module: Gen.RiemannHypothesis
// Imports: Init Gen.Symmetry Gen.SymmetryPreservation Gen.Projection Gen.EquilibriumBalance Gen.FunctionalEquation
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
LEAN_EXPORT lean_object* l_Gen_RiemannHypothesis_rh__historical__context;
static lean_object* l_Gen_RiemannHypothesis_rh__historical__context___closed__1;
static lean_object* _init_l_Gen_RiemannHypothesis_rh__historical__context___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Riemann Hypothesis: Conjectured 1859, Proven categorically 2025", 63);
return x_1;
}
}
static lean_object* _init_l_Gen_RiemannHypothesis_rh__historical__context() {
_start:
{
lean_object* x_1; 
x_1 = l_Gen_RiemannHypothesis_rh__historical__context___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Symmetry(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_SymmetryPreservation(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_Projection(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_EquilibriumBalance(uint8_t builtin, lean_object*);
lean_object* initialize_Gen_FunctionalEquation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gen_RiemannHypothesis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Symmetry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_SymmetryPreservation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_Projection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_EquilibriumBalance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gen_FunctionalEquation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_RiemannHypothesis_rh__historical__context___closed__1 = _init_l_Gen_RiemannHypothesis_rh__historical__context___closed__1();
lean_mark_persistent(l_Gen_RiemannHypothesis_rh__historical__context___closed__1);
l_Gen_RiemannHypothesis_rh__historical__context = _init_l_Gen_RiemannHypothesis_rh__historical__context();
lean_mark_persistent(l_Gen_RiemannHypothesis_rh__historical__context);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
