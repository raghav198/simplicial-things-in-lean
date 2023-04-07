import algebraic_topology.nerve
import algebraic_topology.simplicial_object
import category_theory.adjunction.basic
import category_theory.functor.basic
import category_theory.functor.category

import nerve_helpers
import simplicial_realization

open category_theory quiver category_theory.simplicial_object


variables (C : Type) [category C]

-- define the counit first 



@[simp] lemma sort_of_bundled_cat (T : Type*) [category T] : bundled.α (Cat.of(T)) = T := rfl

def N0_is_hobj : coe_sort (HomotopyRealization.obj (nerve C)) = (nerve C) _[0] := begin
  unfold HomotopyRealization, simp,
  unfold coe_sort, unfold has_coe_to_sort.coe,
  rw sort_of_bundled_cat ((nerve C) _[0]),
  unfold nerve,
end

def counit.obj (X : HomotopyRealization.obj (nerve C)) : C := obj_of_N0 C ((N0_is_hobj C).mp X)

def counit.map' (X Y : HomotopyRealization.obj (nerve C)) (f : @path (nerve C _[0]) underlying X Y) : (counit.obj C X) ⟶ (counit.obj C Y) :=
begin
  induction f with _ _ α_1 α, refine (𝟙 _), 
  dsimp only [counit.obj], simp,
  refine (f_ih ≫ (hom_of_N1 C α)),
end

def counit.map (X Y : HomotopyRealization.obj (nerve C)) := 
quotient.lift (counit.map' C X Y) begin
  intros p q H,
  induction H,
  focus {
    induction H_h with h H_C σ τ ρ,
    
  }
end


def adjoint : HomotopyRealization ⊣ nerve_functor := adjunction.mk_of_unit_counit {
  counit := {
      app := λ a, { obj := λ p, counit.obj a p, map := λ p q α, begin 

          apply counit.map', refine α,
      end}
  }
}

lemma counit_respects_homotopies (C : Type) [category C] (h : (nerve C) _[2]) 
: C = C :=
begin
  refl,
end