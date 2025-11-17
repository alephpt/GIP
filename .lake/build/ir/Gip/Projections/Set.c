// Lean compiler output
// Module: Gip.Projections.Set
// Imports: Init Gip.Basic Gip.Morphisms Mathlib.Data.Finset.Basic Mathlib.CategoryTheory.Category.Basic
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
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_id(lean_object*);
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_compose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Gen_F__S__morphism___closed__1;
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_id___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__S__morphism___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__S__morphism(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_FinSetObj_card___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Gen_F__S__morphism___closed__2;
LEAN_EXPORT lean_object* l_Gen_F__S__obj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Gen_FinSetObj_card(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_instDecidableEqFinSetObj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Gen_F__S__obj(lean_object*);
LEAN_EXPORT uint8_t l_Gen_instDecidableEqFinSetObj(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Gen_instDecidableEqFinSetObj(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Gip_Projections_Set_0__Gen_decEqFinSetObj____x40_Gip_Projections_Set___hyg_17_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Gen_instDecidableEqFinSetObj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Gen_instDecidableEqFinSetObj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Gen_FinSetObj_card(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_FinSetObj_card___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_FinSetObj_card(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_id(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_id___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_FinSetMorphism_id(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_FinSetMorphism_compose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Gen_F__S__obj(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_box(1);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_F__S__obj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Gen_F__S__obj(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_F__S__morphism___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Gen_F__S__obj(x_1);
return x_2;
}
}
static lean_object* _init_l_Gen_F__S__morphism___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Gen_F__S__morphism___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Gen_F__S__morphism(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Gen_F__S__obj(x_2);
x_9 = l_Gen_F__S__obj(x_5);
x_10 = l_Gen_F__S__morphism(x_2, x_5, x_6);
x_11 = l_Gen_F__S__morphism(x_5, x_2, x_7);
lean_inc(x_8);
x_12 = lean_alloc_ctor(7, 5, 0);
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
x_13 = l_Gen_F__S__morphism___closed__2;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = l_Gen_F__S__obj(x_1);
x_18 = l_Gen_F__S__obj(x_14);
x_19 = l_Gen_F__S__obj(x_2);
x_20 = l_Gen_F__S__morphism(x_1, x_14, x_15);
x_21 = l_Gen_F__S__morphism(x_14, x_2, x_16);
x_22 = lean_alloc_ctor(7, 5, 0);
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
x_26 = l_Gen_F__S__obj(x_1);
x_27 = l_Gen_F__S__obj(x_23);
x_28 = l_Gen_F__S__obj(x_2);
x_29 = l_Gen_F__S__morphism(x_1, x_23, x_24);
x_30 = l_Gen_F__S__morphism(x_23, x_2, x_25);
x_31 = lean_alloc_ctor(7, 5, 0);
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
x_35 = l_Gen_F__S__obj(x_1);
x_36 = l_Gen_F__S__obj(x_32);
x_37 = l_Gen_F__S__obj(x_2);
x_38 = l_Gen_F__S__morphism(x_1, x_32, x_33);
x_39 = l_Gen_F__S__morphism(x_32, x_2, x_34);
x_40 = lean_alloc_ctor(7, 5, 0);
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
x_45 = l_Gen_F__S__obj(x_2);
x_46 = l_Gen_F__S__obj(x_42);
x_47 = l_Gen_F__S__morphism(x_2, x_42, x_43);
x_48 = l_Gen_F__S__morphism(x_42, x_2, x_44);
lean_inc(x_45);
x_49 = lean_alloc_ctor(7, 5, 0);
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
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_50, x_53);
x_55 = lean_nat_dec_eq(x_54, x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_nat_sub(x_54, x_53);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_add(x_56, x_57);
lean_dec(x_56);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_54);
x_60 = lean_box(5);
return x_60;
}
}
else
{
uint8_t x_61; lean_object* x_62; 
x_61 = 0;
x_62 = lean_sorry(x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 3);
x_65 = lean_ctor_get(x_3, 4);
x_66 = l_Gen_F__S__obj(x_1);
x_67 = l_Gen_F__S__obj(x_63);
x_68 = l_Gen_F__S__obj(x_2);
x_69 = l_Gen_F__S__morphism(x_1, x_63, x_64);
x_70 = l_Gen_F__S__morphism(x_63, x_2, x_65);
x_71 = lean_alloc_ctor(7, 5, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
return x_71;
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_72, x_75);
x_77 = lean_nat_dec_eq(x_76, x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_nat_sub(x_76, x_75);
lean_dec(x_76);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_add(x_78, x_79);
lean_dec(x_78);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_76);
x_82 = lean_box(1);
return x_82;
}
}
else
{
lean_object* x_83; 
x_83 = lean_box(0);
return x_83;
}
}
case 7:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_3, 1);
x_85 = lean_ctor_get(x_3, 3);
x_86 = lean_ctor_get(x_3, 4);
x_87 = l_Gen_F__S__obj(x_1);
x_88 = l_Gen_F__S__obj(x_84);
x_89 = l_Gen_F__S__obj(x_2);
x_90 = l_Gen_F__S__morphism(x_1, x_84, x_85);
x_91 = l_Gen_F__S__morphism(x_84, x_2, x_86);
x_92 = lean_alloc_ctor(7, 5, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set(x_92, 4, x_91);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; 
x_93 = 0;
x_94 = lean_sorry(x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_3, 1);
x_96 = lean_ctor_get(x_3, 3);
x_97 = lean_ctor_get(x_3, 4);
x_98 = l_Gen_F__S__obj(x_1);
x_99 = l_Gen_F__S__obj(x_95);
x_100 = l_Gen_F__S__obj(x_2);
x_101 = l_Gen_F__S__morphism(x_1, x_95, x_96);
x_102 = l_Gen_F__S__morphism(x_95, x_2, x_97);
x_103 = lean_alloc_ctor(7, 5, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_102);
return x_103;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Gen_F__S__morphism___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Gen_F__S__morphism(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__2_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_dec_eq(x_8, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_sub(x_8, x_7);
lean_dec(x_8);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_inc(x_3);
return x_3;
}
}
else
{
lean_dec(x_4);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Gip_Projections_Set_0__Gen_F__S__morphism_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Gip_Morphisms(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Category_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Gip_Projections_Set(uint8_t builtin, lean_object* w) {
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
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Category_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Gen_F__S__morphism___closed__1 = _init_l_Gen_F__S__morphism___closed__1();
lean_mark_persistent(l_Gen_F__S__morphism___closed__1);
l_Gen_F__S__morphism___closed__2 = _init_l_Gen_F__S__morphism___closed__2();
lean_mark_persistent(l_Gen_F__S__morphism___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
