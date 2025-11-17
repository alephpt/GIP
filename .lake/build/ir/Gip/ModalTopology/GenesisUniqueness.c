// Lean compiler output
// Module: Gip.ModalTopology.GenesisUniqueness
// Imports: Init Gip.Basic Gip.Morphisms Gip.ModalTopology.MetricSpace Mathlib.Topology.MetricSpace.Basic Mathlib.Analysis.SpecificLimits.Basic
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
LEAN_EXPORT lean_object* l_Gen_ModalTopology_coherenceOperator__unit(lean_object*);
LEAN_EXPORT lean_object* l_Gen_ModalTopology_genesis__unit;
LEAN_EXPORT lean_object* l_Gen_ModalTopology_coherenceOperator__unit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_ModalTopology_coherenceOperator__unit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(3);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_ModalTopology_coherenceOperator__unit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_ModalTopology_coherenceOperator__unit(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_ModalTopology_genesis__unit() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(3);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Morphisms(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_ModalTopology_MetricSpace(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecificLimits_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gip_ModalTopology_GenesisUniqueness(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gip_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gip_Morphisms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gip_ModalTopology_MetricSpace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecificLimits_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_ModalTopology_genesis__unit = _init_l_Gen_ModalTopology_genesis__unit();
lean_mark_persistent(l_Gen_ModalTopology_genesis__unit);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
