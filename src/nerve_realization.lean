import algebraic_topology.nerve
import algebraic_topology.topological_simplex
import category_theory.adjunction.basic
import category_theory.adjunction.comma
import category_theory.limits.presheaf

open category_theory opposite

def my_nerve : (Cat ⥤ sSet) := 
  colimit_adj.restricted_yoneda simplex_category.to_Cat

noncomputable def nerve_adjoint : (sSet ⥤ Top) := 
colimit_adj.extend_along_yoneda simplex_category.to_Top


lemma kan_extension_nerve : colimit_adj.restricted_yoneda simplex_category.to_Cat = nerve_functor := begin
  apply functor.hext, {
    intro X, unfold colimit_adj.restricted_yoneda,
    simp,
    apply functor.hext, {
      intro n, rw functor.comp_obj,
      have : (nerve X).obj n = ((simplex_category.to_Cat.obj n.unop) ⥤ X), simp,
      rw this, refl,
    }, {
      intros n m f,
      rw functor.comp_map, 
      refl,
    }
  }, {
    intros X Y F, simp, refl,
  }
end