import algebraic_topology.nerve
import algebraic_topology.topological_simplex
import category_theory.adjunction.basic
import category_theory.adjunction.comma
import category_theory.limits.presheaf

open category_theory opposite

def my_nerve : (Cat ⥤ sSet) := 
  colimit_adj.restricted_yoneda simplex_category.to_Cat

lemma i_hate_yoneda (X : Cat) (Y : Catᵒᵖ) : 
      (yoneda.obj X).obj Y = (Y.unop ⟶ X) := by simp

lemma i_hate_op (X : simplex_categoryᵒᵖ) (F : simplex_category ⥤ Cat) :
      unop (F.op.obj X) = F.obj X.unop := by simp


lemma helper_ext (X : Cat) (Y : simplex_categoryᵒᵖ) :
(yoneda.obj X).obj (simplex_category.to_Cat.op.obj Y) = (nerve X).obj Y := begin
  have : (nerve X).obj Y = ((simplex_category.to_Cat.obj Y.unop) ⥤ X), simp,
  rw this,
  rw i_hate_yoneda,
  rw i_hate_op Y simplex_category.to_Cat,
  refl,
end

noncomputable lemma helper (X : Cat) : 
simplex_category.to_Cat.op ⋙ yoneda.obj X ≅ nerve X := 
by refine {
  hom := { app := begin
    intro Y, rw functor.comp_obj,
    rw helper_ext,
    exact 𝟙 _,
  end },
  inv := { app := begin
    intro Y, rw functor.comp_obj,
    rw helper_ext,
    exact 𝟙 _,
  end },
}

#check my_nerve.map

noncomputable lemma nerve_is_a_nerve : my_nerve ≅ nerve_functor := {
  hom := { 
    app := λ Y, begin
      unfold my_nerve, unfold colimit_adj.restricted_yoneda, simp, 
      apply (helper Y).hom,
    end,
    naturality' := begin
      intros, simp,

        

    end

  },
  inv := { 
    app := λ Y, begin
      unfold my_nerve, unfold colimit_adj.restricted_yoneda, simp,
      apply (helper Y).inv,
    end,
    naturality' := sorry
  },
}