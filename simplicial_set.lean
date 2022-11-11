import algebraic_topology.simplex_category
import algebraic_topology.simplicial_object
import algebraic_topology.nerve
import category_theory.category.basic
import category_theory.functor.basic
import data.finset.basic
import data.fin.basic
import data.nat.basic
import tactic

open category_theory
open finset

structure finset_hom {n : nat} (x y : fin n) := 
mk :: (eps : nat) (H : (x.val + eps = y.val))

instance (n : nat) : category (fin n) := by refine {
    hom := finset_hom,
    id := λ n, finset_hom.mk 0 rfl,
    comp := begin
      intros X Y Z f g,
      apply finset_hom.mk (f.eps + g.eps), 
      rw ← add_assoc, rw f.H, rw g.H,
    end,
    id_comp' := begin
      intros, unfold category_struct.id, unfold category_struct.comp,
      simp, destruct f, simp, intros, rw a,
    end,
    comp_id' := begin
      intros, unfold category_struct.id, unfold category_struct.comp,
      simp, destruct f, simp, intros, rw a,
    end,
    assoc' := begin
      intros, unfold category_struct.comp, simp, rw add_assoc,
    end
}

class monotone_function {n m : ℕ} (f : (fin n) → (fin m)) : Prop := 
(monotone : ∀ (x y : fin n), (x ≤ y) → ((f x) ≤ (f y)))

def coface {n} (i : fin (n + 1)) : fin n → fin (n + 1) :=
  λ x, if x.cast_succ < i then x.cast_succ else x.succ


-- lemma coface_monotone {n : ℕ} (i : fin $ n + 1) : monotone (coface i) := begin
  
-- end

instance {n : ℕ} (i : fin (n + 1)) : monotone_function (coface i) := by refine {
  monotone := λ x y H, (if x.cast_succ < i then begin 
  
  end else (if y.cast_succ < i then begin 
  
  end else begin 
  
  end))
  
  
  begin
    intros x y H,
    unfold coface,
    split_ifs, simp, assumption, 

  end
}

-- def coface (n : ℕ) (i : fin n) : (fin n) → (fin (n + 1)) := 
--     λ x, if x < i then x else fin.mk (x.val + 1) begin
--         destruct x, intro, simp,
--     end

-- #check ite


-- instance (n : ℕ) (i : fin n) : monotone_function (coface n i) := by refine {
--   monotone := begin
--     intros x y h,
--     unfold coface, 
--     have xi_dec : (decidable (x < i)), apply fin.decidable_lt,
--     have yi_dec : (decidable (y < i)), apply fin.decidable_lt,
--     cases xi_dec; cases yi_dec,
    
--     -- easy
--     rw if_neg, rw if_neg, simp, repeat {assumption},
--     -- disgusting
--     rw if_neg, rw if_pos,
--     have : x < i, 
--       cases (lt_or_eq_of_le h), 
--       apply (lt_trans h_1 yi_dec),
--       rw h_1, assumption,
--     contradiction, repeat {assumption},
--     -- easy?
--     rw if_pos, rw if_neg, simp, 

--   end
-- }

-- -- instance ordinal_category : category nat := by refine {
-- --   hom := λ n m, (fin n) ⥤ (fin m),
-- --   id := λ X, 𝟭 (fin X),
-- --   comp := λ X Y Z f g, f ⋙ g,
-- --   id_comp' := begin
-- --     intros, apply functor.comp_id,
-- --   end,
-- --   comp_id' := begin
-- --     intros, apply functor.comp_id,
-- --   end,
-- --   assoc' := begin
-- --     intros, simp, unfold functor.comp,
    
-- --   end
-- -- }