import algebraic_topology.nerve
import algebraic_topology.simplicial_object
import category_theory.adjunction.basic
import category_theory.functor.basic
import category_theory.functor.category

import simplicial_realization

open category_theory quiver category_theory.simplicial_object

variables (C : Type*) [category C]

-- define the counit first 
def point' : (simplex_category.skeletal_functor.obj (simplex_category.mk 0)) := begin
  simp, refine 0,
end

def obj' (n : fin 2) : (simplex_category.skeletal_functor.obj (simplex_category.mk 1)) := begin
  simp, refine n,
end

def arrow' : (obj' 0) ⟶ (obj' 1) := begin
  have H := nat.le_of_lt(nat.lt.base 0),
  refine ulift.up (plift.up H),
end

def obj (n : fin 2) : (simplex_category.to_Cat.obj (simplex_category.mk 1)) := begin
  simp, refine (obj' n),
end

#check simplex_category.to_Cat.map (simplex_category.δ 1)


def arrow : (obj 0) ⟶ (obj 1) := arrow'

def point : ((simplex_category.to_Cat.obj (simplex_category.mk 0))) := point'

lemma d1' : (simplex_category.skeletal_functor.map (simplex_category.δ 1)).to_fun point = (obj' 0) :=
begin
  simp, dsimp [obj'], dsimp [simplex_category.hom.to_order_hom],
  dsimp [simplex_category.δ], dsimp [simplex_category.hom.mk],
  dsimp [point], dsimp [point'], simp, refl,
end

-- i dont know if theres a better way to do this but i also do not care
lemma d1 : (simplex_category.to_Cat.map (simplex_category.δ 1)).obj point = (obj 0) := begin
  
  simp,
  dsimp [forget₂], dsimp [has_forget₂.forget₂],


  dsimp [obj], dsimp [obj'], 
  dsimp [simplex_category.hom.to_order_hom],
  dsimp [simplex_category.δ],
  dsimp [simplex_category.hom.mk],
  dsimp [point], dsimp [point'],
  dsimp [order_hom_class.to_lattice_hom],
  dsimp [coe], dsimp [lift_t], unfold has_lift_t.lift,
  unfold coe_t, unfold has_coe_t.coe,

  unfold coe_fn, unfold has_coe_to_fun.coe, simp,
  unfold coe_fn, unfold has_coe_to_fun.coe, unfold fun_like.coe,

  simp, refl,
  
end

lemma d0 : (simplex_category.to_Cat.map (simplex_category.δ 0)).obj point = (obj 1) := begin
  
  simp,
  dsimp [forget₂], dsimp [has_forget₂.forget₂],


  dsimp [obj], dsimp [obj'], 
  dsimp [simplex_category.hom.to_order_hom],
  dsimp [simplex_category.δ],
  dsimp [simplex_category.hom.mk],
  dsimp [point], dsimp [point'],
  dsimp [order_hom_class.to_lattice_hom],
  dsimp [coe], dsimp [lift_t], unfold has_lift_t.lift,
  unfold coe_t, unfold has_coe_t.coe,

  unfold coe_fn, unfold has_coe_to_fun.coe, simp,
  unfold coe_fn, unfold has_coe_to_fun.coe, unfold fun_like.coe,

  simp, refl,
  
end

#check congr_fun
def counit.obj (X : HomotopyRealization.obj (nerve C)) : C := X.obj point
def one_simplex_to_morphsim {a b : nerve C _[0]} (f : a ⟶ b) : (counit.obj C a) ⟶ (counit.obj C b) := begin
  destruct f, intros, 
  unfold nerve at val, simp at val,
  unfold δ at property, 
  -- simp at property,
  destruct property, intros,
  dsimp [counit.obj], subst left, subst right,
  -- have H := val.map arrow,

  have H0 : (nerve C).map (simplex_category.δ 0).op val = ((simplex_category.to_Cat.map (simplex_category.δ 0).op.unop)) ⋙ val,
  refl,
  have H1 : (nerve C).map (simplex_category.δ 1).op val = ((simplex_category.to_Cat.map (simplex_category.δ 1).op.unop)) ⋙ val,
  refl,

  have H2 : (((nerve C).map (simplex_category.δ 1).op val).obj point) ⟶ (((nerve C).map (simplex_category.δ 0).op val).obj point) = ((((simplex_category.to_Cat.map (simplex_category.δ 1).op.unop)) ⋙ val).obj point) ⟶ ((((simplex_category.to_Cat.map (simplex_category.δ 0).op.unop)) ⋙ val).obj point),
  rw H0, rw H1,

  

  rw d1,
end

def counit.map' (X Y : HomotopyRealization.obj (nerve C)) (f : @path (nerve C _[0]) underlying X Y) : (counit.obj C X) ⟶ (counit.obj C Y) :=
begin
  induction f with _ _ α_1 α, refine (𝟙 _), 
  have H := α.val,
  have H' := α.val.map arrow,
  refine (f_ih ≫ (α.val.map arrow)),
end

-- def counit.map (X Y : (HomotopyRealization.obj (nerve C))) (f : X ⟶ Y) : 
-- (counit.obj C X) ⟶  (counit.obj C Y) := begin
--   dsimp [hom] at f, dsimp [Cat.of] at f, dsimp [bundled.of] at f,
--   dsimp [hom] at f,
--   have H := pick_rep f, cases H, --revert H, introsrintro ⟨f', frw⟩,
  
-- end


def adjoint : HomotopyRealization ⊣ nerve_functor := adjunction.mk_of_unit_counit {
  counit := {
      app := λ a, { obj := λ p, counit.obj a p, map := λ p q α, begin 
          apply counit.map, refine α,
      end}
  }
}

lemma counit_respects_homotopies (C : Type) [category C] (h : (nerve C) _[2]) 
: C = C :=
begin
  refl,
end