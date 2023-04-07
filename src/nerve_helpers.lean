import algebraic_topology.nerve
import algebraic_topology.simplicial_object
import category_theory.category.basic

import categorical_simplices
import path_homotopy

open category_theory quiver category_theory.simplicial_object

variables (C : Type) [category C]

def functor_of_simplex {n} : ((nerve C) _[n]) → (simplex_category.to_Cat.obj (simplex_category.mk n)) ⥤ C :=
begin
  dsimp only [nerve],
  rw opposite.unop_op, refine id,
end

notation `↟`:max x:max := functor_of_simplex x

lemma nerve_face (α : (nerve C) _[1]) {n} : (nerve C).δ n α = ((simplex_category.to_Cat.map ((simplex_category.δ n).op.unop)) ⋙ α)
:= begin
  simp, congr,
end

def obj_of_N0 (α : nerve C _[0]) : C := α.obj point

def hom_of_N1 {a b : nerve C _[0]} (f : a ⟶ b) : (obj_of_N0 C a) ⟶ (obj_of_N0 C b) :=
begin
  destruct f, rintros α ⟨Hl, Hr⟩ _,
  dsimp only [obj_of_N0],
  rw ← Hl, rw ← Hr,
  repeat {rw nerve_face},
  repeat {rw functor.comp_obj},

  dsimp only [point],
  unfold hom.unop, unfold hom.op,
  repeat {rw face_functor},
  refine α.map arrow,
end

def triangle_of_N2 {a b c : nerve C _[0]} (h : triangle_at a b c) : 
  ((obj_of_N0 C a) ⟶ (obj_of_N0 C c))×((obj_of_N0 C c) ⟶ (obj_of_N0 C b)) :=
begin
  split,
  refine hom_of_N1 C (d2_qedge h),
  refine hom_of_N1 C (d0_qedge h),
end

variables {a b c : nerve C _[0]} (h : triangle_at a b c)

def d0_is_d0 {a b c : nerve C _[0]} (h : triangle_at a b c) : 
((nerve C).δ 0 h.val).map arrow = (h.val.map (triangle.fst))

def comp_of_N2 {a b c : nerve C _[0]} (h : triangle_at a b c) : 
(hom_of_N1 C (d1_qedge h)) = ((hom_of_N1 C (d2_qedge h)) ≫ ((hom_of_N1 C (d0_qedge h)))) :=
begin
  dsimp [d0_qedge, d1_qedge, d2_qedge], 
  dsimp only [edge_to_qedge],
  dsimp only [hom_of_N1],
end
 