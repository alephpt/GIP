// Lean compiler output
// Module: Gip.Projections.Comp
// Imports: Init Gip.Projections.Ring
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
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__obj(lean_object*);
LEAN_EXPORT lean_object* l_Gen_CompMorphism_compose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_CompMorphism_id___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__comp__morphism(lean_object*, lean_object*, lean_object*);
static lean_object* l_Gen_Ring__to__Comp__morphism___closed__2;
lean_object* l_Gen_F__R__morphism(lean_object*, lean_object*, lean_object*);
static lean_object* l_Gen_Ring__to__Comp__morphism___closed__1;
LEAN_EXPORT lean_object* l_Gen_instDecidableEqCompObj___boxed(lean_object*, lean_object*);
static lean_object* l_Gen_zeta__morphism___closed__2;
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* l_Gen_zeta__morphism;
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18____boxed(lean_object*, lean_object*);
static lean_object* l_Gen_zeta__morphism___closed__1;
LEAN_EXPORT lean_object* l_Gen_F__comp__morphism___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_CompMorphism_id(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__morphism___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__comp__obj(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Gen_instDecidableEqCompObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__comp__obj___boxed(lean_object*);
lean_object* l_Gen_F__R__obj(lean_object*);
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__obj___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__morphism(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Gen_instDecidableEqCompObj(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Gip_Projections_Comp_0__Gen_decEqCompObj____x40_Gip_Projections_Comp___hyg_18_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_instDecidableEqCompObj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Gen_instDecidableEqCompObj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_CompMorphism_id(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Gen_CompMorphism_id___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_CompMorphism_id(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_CompMorphism_compose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__obj(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__obj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_Ring__to__Comp__obj(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_Ring__to__Comp__morphism___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zero", 4);
return x_1;
}
}
static lean_object* _init_l_Gen_Ring__to__Comp__morphism___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Gen_Ring__to__Comp__morphism___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__morphism(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
case 3:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_sorry(x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = l_Gen_Ring__to__Comp__obj(x_2);
x_11 = l_Gen_Ring__to__Comp__obj(x_7);
x_12 = l_Gen_Ring__to__Comp__morphism(x_2, x_7, x_8);
x_13 = l_Gen_Ring__to__Comp__morphism(x_7, x_2, x_9);
lean_inc(x_10);
x_14 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_13);
return x_14;
}
}
}
case 1:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_15; 
x_15 = l_Gen_Ring__to__Comp__morphism___closed__2;
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = l_Gen_Ring__to__Comp__obj(x_1);
x_20 = l_Gen_Ring__to__Comp__obj(x_16);
x_21 = l_Gen_Ring__to__Comp__obj(x_2);
x_22 = l_Gen_Ring__to__Comp__morphism(x_1, x_16, x_17);
x_23 = l_Gen_Ring__to__Comp__morphism(x_16, x_2, x_18);
x_24 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
return x_24;
}
}
default: 
{
if (lean_obj_tag(x_3) == 3)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = lean_sorry(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_3, 4);
x_30 = l_Gen_Ring__to__Comp__obj(x_1);
x_31 = l_Gen_Ring__to__Comp__obj(x_27);
x_32 = l_Gen_Ring__to__Comp__obj(x_2);
x_33 = l_Gen_Ring__to__Comp__morphism(x_1, x_27, x_28);
x_34 = l_Gen_Ring__to__Comp__morphism(x_27, x_2, x_29);
x_35 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
return x_35;
}
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_3, 3);
x_38 = lean_ctor_get(x_3, 4);
x_39 = l_Gen_Ring__to__Comp__obj(x_1);
x_40 = l_Gen_Ring__to__Comp__obj(x_36);
x_41 = l_Gen_Ring__to__Comp__obj(x_2);
x_42 = l_Gen_Ring__to__Comp__morphism(x_1, x_36, x_37);
x_43 = l_Gen_Ring__to__Comp__morphism(x_36, x_2, x_38);
x_44 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_45; 
x_45 = lean_box(0);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
x_49 = l_Gen_Ring__to__Comp__obj(x_2);
x_50 = l_Gen_Ring__to__Comp__obj(x_46);
x_51 = l_Gen_Ring__to__Comp__morphism(x_2, x_46, x_47);
x_52 = l_Gen_Ring__to__Comp__morphism(x_46, x_2, x_48);
lean_inc(x_49);
x_53 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
return x_53;
}
}
default: 
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 3);
x_58 = lean_ctor_get(x_3, 4);
x_59 = l_Gen_Ring__to__Comp__obj(x_1);
x_60 = l_Gen_Ring__to__Comp__obj(x_56);
x_61 = l_Gen_Ring__to__Comp__obj(x_2);
x_62 = l_Gen_Ring__to__Comp__morphism(x_1, x_56, x_57);
x_63 = l_Gen_Ring__to__Comp__morphism(x_56, x_2, x_58);
x_64 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_63);
return x_64;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_3, 1);
x_66 = lean_ctor_get(x_3, 3);
x_67 = lean_ctor_get(x_3, 4);
x_68 = l_Gen_Ring__to__Comp__obj(x_1);
x_69 = l_Gen_Ring__to__Comp__obj(x_65);
x_70 = l_Gen_Ring__to__Comp__obj(x_2);
x_71 = l_Gen_Ring__to__Comp__morphism(x_1, x_65, x_66);
x_72 = l_Gen_Ring__to__Comp__morphism(x_65, x_2, x_67);
x_73 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_72);
return x_73;
}
case 1:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
lean_inc(x_74);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_3, 1);
x_78 = lean_ctor_get(x_3, 3);
x_79 = lean_ctor_get(x_3, 4);
x_80 = l_Gen_Ring__to__Comp__obj(x_1);
x_81 = l_Gen_Ring__to__Comp__obj(x_77);
x_82 = l_Gen_Ring__to__Comp__obj(x_2);
x_83 = l_Gen_Ring__to__Comp__morphism(x_1, x_77, x_78);
x_84 = l_Gen_Ring__to__Comp__morphism(x_77, x_2, x_79);
x_85 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_84);
return x_85;
}
}
default: 
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_ctor_get(x_3, 1);
x_89 = lean_ctor_get(x_3, 3);
x_90 = lean_ctor_get(x_3, 4);
x_91 = l_Gen_Ring__to__Comp__obj(x_1);
x_92 = l_Gen_Ring__to__Comp__obj(x_88);
x_93 = l_Gen_Ring__to__Comp__obj(x_2);
x_94 = l_Gen_Ring__to__Comp__morphism(x_1, x_88, x_89);
x_95 = l_Gen_Ring__to__Comp__morphism(x_88, x_2, x_90);
x_96 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
return x_96;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_Ring__to__Comp__morphism___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_Ring__to__Comp__morphism(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_F__comp__obj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Gen_F__R__obj(x_1);
x_3 = l_Gen_Ring__to__Comp__obj(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_F__comp__obj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_F__comp__obj(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_F__comp__morphism(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Gen_F__R__obj(x_1);
x_5 = l_Gen_F__R__obj(x_2);
x_6 = l_Gen_F__R__morphism(x_1, x_2, x_3);
x_7 = l_Gen_Ring__to__Comp__morphism(x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Gen_F__comp__morphism___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_F__comp__morphism(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_6);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_dec(x_12);
lean_dec(x_11);
lean_inc(x_4);
return x_4;
}
case 3:
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_2);
x_15 = lean_apply_11(x_12, x_2, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_apply_11(x_12, x_2, x_2, x_16, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_17;
}
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 4);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_apply_5(x_11, x_2, x_2, x_18, x_19, x_20);
return x_21;
}
}
}
case 1:
{
lean_dec(x_12);
lean_dec(x_6);
if (lean_obj_tag(x_3) == 3)
{
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 4);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_apply_5(x_11, x_1, x_2, x_22, x_23, x_24);
return x_25;
}
}
default: 
{
lean_dec(x_12);
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_apply_1(x_6, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 4);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_apply_5(x_11, x_1, x_2, x_28, x_29, x_30);
return x_31;
}
}
}
}
case 1:
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 4);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_apply_5(x_11, x_1, x_2, x_32, x_33, x_34);
return x_35;
}
case 1:
{
lean_dec(x_9);
if (lean_obj_tag(x_3) == 1)
{
lean_dec(x_11);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 4);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_apply_5(x_11, x_2, x_2, x_36, x_37, x_38);
return x_39;
}
}
default: 
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_3);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_apply_1(x_9, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_9);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 4);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_apply_5(x_11, x_1, x_2, x_42, x_43, x_44);
return x_45;
}
}
}
}
default: 
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_8);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 4);
lean_inc(x_48);
lean_dec(x_3);
x_49 = lean_apply_5(x_11, x_1, x_2, x_46, x_47, x_48);
return x_49;
}
case 1:
{
lean_dec(x_8);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_apply_2(x_10, x_50, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 4);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_apply_5(x_11, x_1, x_2, x_53, x_54, x_55);
return x_56;
}
}
default: 
{
lean_dec(x_10);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_apply_1(x_8, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_8);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_apply_5(x_11, x_1, x_2, x_59, x_60, x_61);
return x_62;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Gip_Projections_Comp_0__Gen_Ring__to__Comp__morphism_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l_Gen_zeta__morphism___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zeta", 4);
return x_1;
}
}
static lean_object* _init_l_Gen_zeta__morphism___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Gen_zeta__morphism___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_zeta__morphism() {
_start:
{
lean_object* x_1; 
x_1 = l_Gen_zeta__morphism___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_9);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_apply_5(x_9, x_2, x_2, x_11, x_12, x_13);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 3)
{
lean_dec(x_9);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_apply_5(x_9, x_1, x_2, x_15, x_16, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 4);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_apply_5(x_9, x_1, x_2, x_19, x_20, x_21);
return x_22;
}
}
}
case 1:
{
lean_dec(x_10);
lean_dec(x_7);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_apply_5(x_9, x_1, x_2, x_23, x_24, x_25);
return x_26;
}
case 1:
{
lean_dec(x_8);
if (lean_obj_tag(x_3) == 1)
{
lean_dec(x_9);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 4);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_apply_5(x_9, x_2, x_2, x_27, x_28, x_29);
return x_30;
}
}
default: 
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_3);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_apply_1(x_8, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 4);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_apply_5(x_9, x_1, x_2, x_33, x_34, x_35);
return x_36;
}
}
}
}
default: 
{
lean_dec(x_8);
if (lean_obj_tag(x_2) == 2)
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_apply_1(x_7, x_37);
return x_38;
}
case 5:
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_3, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
lean_ctor_set(x_3, 1, x_43);
lean_ctor_set(x_3, 0, x_42);
x_44 = lean_apply_9(x_10, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_apply_9(x_10, x_1, x_2, x_47, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_48;
}
}
case 6:
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_ctor_set(x_3, 0, x_51);
lean_inc(x_1);
x_52 = lean_apply_9(x_10, x_1, x_1, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_1);
x_55 = lean_apply_9(x_10, x_1, x_1, x_54, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_55;
}
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
lean_dec(x_7);
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 4);
lean_inc(x_58);
lean_dec(x_3);
x_59 = lean_apply_5(x_9, x_1, x_2, x_56, x_57, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_10);
lean_dec(x_7);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 4);
lean_inc(x_62);
lean_dec(x_3);
x_63 = lean_apply_5(x_9, x_1, x_2, x_60, x_61, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Gip_Projections_Comp_0__Gen_F__R__morphism_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Projections_Ring(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gip_Projections_Comp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Gip_Projections_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_Ring__to__Comp__morphism___closed__1 = _init_l_Gen_Ring__to__Comp__morphism___closed__1();
lean_mark_persistent(l_Gen_Ring__to__Comp__morphism___closed__1);
l_Gen_Ring__to__Comp__morphism___closed__2 = _init_l_Gen_Ring__to__Comp__morphism___closed__2();
lean_mark_persistent(l_Gen_Ring__to__Comp__morphism___closed__2);
l_Gen_zeta__morphism___closed__1 = _init_l_Gen_zeta__morphism___closed__1();
lean_mark_persistent(l_Gen_zeta__morphism___closed__1);
l_Gen_zeta__morphism___closed__2 = _init_l_Gen_zeta__morphism___closed__2();
lean_mark_persistent(l_Gen_zeta__morphism___closed__2);
l_Gen_zeta__morphism = _init_l_Gen_zeta__morphism();
lean_mark_persistent(l_Gen_zeta__morphism);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
