import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.category.Cat
import category_theory.category.preorder

import data.fin.basic

open category_theory category_theory.Cat

instance {n : ℕ} : category (fin n) := preorder.small_category (fin n)

def n_simplex_category (n : simplex_category) : category_theory.Cat :=
  category_theory.Cat.of(fin $ n.len + 1)

variable X : simplex_category
variable f : ℕ → ℕ 
#check order_hom.to_fun $ simplex_category.hom.to_order_hom (𝟙 X)
#check @functor.ext 


def n_simplex_category_functor : simplex_category ⥤ category_theory.Cat := {
  obj := n_simplex_category,
  map := λ n m f, { 
    obj := f.to_order_hom,
    map := λ X Y g, hom_of_le $ f.to_order_hom.monotone $ le_of_hom g,
  },
  map_id' := begin
    intros, 
    
  end,
}