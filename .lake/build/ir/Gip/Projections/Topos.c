// Lean compiler output
// Module: Gip.Projections.Topos
// Imports: Init Gip.Basic Gip.Morphisms Mathlib.CategoryTheory.Category.Basic Mathlib.CategoryTheory.Functor.Basic
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
LEAN_EXPORT lean_object* l_Gen_instDecidableEqToposObj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_id___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_id(lean_object*);
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_compose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__T__morphism___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__T__morphism(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__T__obj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__T__obj(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Gen_instDecidableEqToposObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
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
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Gen_instDecidableEqToposObj(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Gip_Projections_Topos_0__Gen_decEqToposObj____x40_Gip_Projections_Topos___hyg_17_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_instDecidableEqToposObj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Gen_instDecidableEqToposObj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_id(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_box(1);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_id___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_ToposMorphism_id(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_ToposMorphism_compose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Gen_F__T__obj(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_box(1);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_F__T__obj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_F__T__obj(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_F__T__morphism(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 4);
x_8 = l_Gen_F__T__obj(x_2);
x_9 = l_Gen_F__T__obj(x_5);
x_10 = l_Gen_F__T__morphism(x_2, x_5, x_6);
x_11 = l_Gen_F__T__morphism(x_5, x_2, x_7);
lean_inc(x_8);
x_12 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
return x_12;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_13; 
x_13 = lean_box(3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = l_Gen_F__T__obj(x_1);
x_18 = l_Gen_F__T__obj(x_14);
x_19 = l_Gen_F__T__obj(x_2);
x_20 = l_Gen_F__T__morphism(x_1, x_14, x_15);
x_21 = l_Gen_F__T__morphism(x_14, x_2, x_16);
x_22 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = l_Gen_F__T__obj(x_1);
x_27 = l_Gen_F__T__obj(x_23);
x_28 = l_Gen_F__T__obj(x_2);
x_29 = l_Gen_F__T__morphism(x_1, x_23, x_24);
x_30 = l_Gen_F__T__morphism(x_23, x_2, x_25);
x_31 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_30);
return x_31;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = l_Gen_F__T__obj(x_1);
x_36 = l_Gen_F__T__obj(x_32);
x_37 = l_Gen_F__T__obj(x_2);
x_38 = l_Gen_F__T__morphism(x_1, x_32, x_33);
x_39 = l_Gen_F__T__morphism(x_32, x_2, x_34);
x_40 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_39);
return x_40;
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_41; 
x_41 = lean_box(1);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = l_Gen_F__T__obj(x_2);
x_46 = l_Gen_F__T__obj(x_42);
x_47 = l_Gen_F__T__morphism(x_2, x_42, x_43);
x_48 = l_Gen_F__T__morphism(x_42, x_2, x_44);
lean_inc(x_45);
x_49 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_48);
return x_49;
}
}
default: 
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_3, 1);
x_53 = lean_ctor_get(x_3, 3);
x_54 = lean_ctor_get(x_3, 4);
x_55 = l_Gen_F__T__obj(x_1);
x_56 = l_Gen_F__T__obj(x_52);
x_57 = l_Gen_F__T__obj(x_2);
x_58 = l_Gen_F__T__morphism(x_1, x_52, x_53);
x_59 = l_Gen_F__T__morphism(x_52, x_2, x_54);
x_60 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
return x_60;
}
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
case 7:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 3);
x_65 = lean_ctor_get(x_3, 4);
x_66 = l_Gen_F__T__obj(x_1);
x_67 = l_Gen_F__T__obj(x_63);
x_68 = l_Gen_F__T__obj(x_2);
x_69 = l_Gen_F__T__morphism(x_1, x_63, x_64);
x_70 = l_Gen_F__T__morphism(x_63, x_2, x_65);
x_71 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
return x_71;
}
default: 
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
x_73 = lean_sorry(x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_ctor_get(x_3, 3);
x_76 = lean_ctor_get(x_3, 4);
x_77 = l_Gen_F__T__obj(x_1);
x_78 = l_Gen_F__T__obj(x_74);
x_79 = l_Gen_F__T__obj(x_2);
x_80 = l_Gen_F__T__morphism(x_1, x_74, x_75);
x_81 = l_Gen_F__T__morphism(x_74, x_2, x_76);
x_82 = lean_alloc_ctor(8, 5, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_81);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_F__T__morphism___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_F__T__morphism(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Gip_Projections_Topos_0__Gen_F__T__morphism_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Morphisms(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Category_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Functor_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gip_Projections_Topos(uint8_t builtin, lean_object* w) {
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
res = initialize_Mathlib_CategoryTheory_Category_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Functor_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
