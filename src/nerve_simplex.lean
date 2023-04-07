import algebraic_topology.simplex_category
import categorical_simplices
import tactic.omega

open category_theory

-- define a functor [n] ⥤ C given a composable 
-- sequence of morphisms in C
universes u v
variables {C : Type u} [category.{v} C]


notation `[[`n`]]` := simplex_category.to_Cat.obj (simplex_category.mk n)



def recursion_on_lt'' {P : Π (x y : ℕ), Type} 
  (inc : Π (i : ℕ), P i (i+1)) 
  (id : Π (i : ℕ), P i i) 
  (trans : Π (i j k : ℕ), P i j → P j k → P i k): 
  Π (i j : ℕ), (i ≤ j) → P i j
| 0 0 h := id 0
| (i'+1) 0 h := sorry -- exfalso
| 0 (j'+1) h := begin
  have H := recursion_on_lt'' 0 j' _,
  sorry, omega,
end
| (i'+1) (j'+1) h := begin
  -- ??
end


def recursion_on_lt' {P : Π (x y : ℕ), Type} 
  (inc : Π (i : ℕ), P i (i+1)) 
  (id : Π (i : ℕ), P i i) 
  (trans : Π (i j k : ℕ), P i j → P j k → P i k): 
  Π (a b : ℕ),  P a (a+b) := begin
    intros,
    induction b, simp, refine id _,
    apply trans a (a+b_n) _, tauto, refine inc _,
end

def recursion_on_lt {P : Π (x y : ℕ), Type} 
  (inc : Π (i : ℕ), P i (i+1)) 
  (id : Π (i : ℕ), P i i) 
  (trans : Π (i j k : ℕ), P i j → P j k → P i k): 
  Π (i j : ℕ), (i ≤ j) → P i j := begin
    intros i j H,
    have : j = i + (j - i), by omega,
    rw this, refine recursion_on_lt' inc id trans i (j - i),
end


namespace composable

inductive composable : ℕ → C → C → Type (max u v)
| nil (X : C) : composable 0 X X
| cons (X Y Z : C) {n : ℕ} (f : X ⟶ Y) (gs : composable n Y Z) : composable (n+1) X Z

def to_hom : Π {n : ℕ}, Π (X Y : C), composable n X Y → (X ⟶ Y)
| 0 _ _ (composable.nil X) := 𝟙 X
| (m+1) X Y (composable.cons _ Z _ f gs) := f ≫ (to_hom Z Y gs)


def obj : Π {n : ℕ} {X Y : C}, composable n X Y → fin (n+1) → C
| _ _ _ (composable.nil X) ⟨0, _⟩ := X
| _ _ _ (composable.nil X) ⟨m+1, _⟩ := X
| _ _ _ (composable.cons X _ _ f gs) ⟨0, _⟩ := X
| _ _ _ (composable.cons _ _ _ f gs) ⟨m+1, _⟩ := obj gs m

end composable



-- def functor_of_composable {n : ℕ} {A B : C} : composable.composable n A B → [[n]] ⥤ C := begin
--   intro fs, split,
--   intro i, induction i, simp at i, refine composable.obj fs i,

--   intros X Y f,
--   induction X, induction Y, simp, 
--   dsimp [simplex_category] at *,
--   have H : X ≤ Y,
--   induction f, induction f,
--   refine f,
--   clear f,
--   induction X with i hi,
--   induction Y with j hj,
  

--   have H' : i ≤ j, by tauto,



--   apply recursion_on_lt,
-- end

-- def composable_of_sequence :
--   Π (n : ℕ), Π (obj : fin (n+2) → C), 
--   Π (map : Π (i : fin (n+1)), obj i.cast_succ ⟶ obj i.succ),
--   composable (obj 0) (obj (n+1))
-- | 0 obj map := composable.hom _ _ (map 0)
-- | (m+1) obj map := begin
--   apply composable.cons (obj 0) (obj (m+1)),
--   refine composable_of_sequence m obj _,
-- end

def functor_of_sequence_helper {n : ℕ} (obj : fin (n+1) → C)
      (map : Π (i : fin (n)), obj i.cast_succ ⟶ obj i.succ) 
      (start : fin n) (len : fin (n+1-start))
      
      : obj start ⟶ obj (start+len) :=
begin
  induction start with start Hstart,
  induction len with len Hlen,
  induction len, simp, refine 𝟙 _,
  refine (len_ih _) ≫ _,
  simp, simp at Hlen, apply nat.lt_trans, omega, refine Hlen,
  simp, refine _ ≫ (map ⟨start+len_n, _⟩) ≫ _,
  simp at Hlen, sorry,
  simp,
end


-- (2 2 : fin 3) i + j := (i + j) mod n
-- i j : fin (n+1) i + j mod (n+1) =/= i+j mod n



lemma helper (i n : ℕ) : i < n + 1 → i ≠ n → i < n := begin
  intros, omega,
end

lemma helper2 (i n k : ℕ) : i < n → k.succ < n + 1 - i → k < n := begin
  intros, omega,
end

-- eq_hom (a b : C) [category C] : (a = b) → (a ⟶ b)
def functor_of_sequence {n : ℕ} (obj : fin (n+1) → C)
      (map : Π (i : fin (n)), obj i.cast_succ ⟶ obj i.succ) : [[n]] ⥤ C :=
begin
  split,
  
  intro i,
  induction i, refine obj i,

  intros X Y f,
  induction X, induction Y, simp, 
  dsimp [simplex_category] at *,
  have H : X ≤ Y,
  induction f, induction f,
  refine f,
  clear f,
  induction X with i hi,
  induction Y with j hj,
  

  have H' : i ≤ j, by tauto,
  have helper : Π (k : fin (n+1-i)), obj ⟨i,hi⟩ ⟶ obj (⟨i,hi⟩ + k), {
  intros, induction k, induction k_val,

    simp, refine 𝟙 _,
    simp, refine (k_val_ih _) ≫ _, apply nat.lt_trans, omega, refine k_property,
    have k_property' : k_val_n < n + 1 - i, apply nat.lt_trans, omega, refine k_property,

    have i_property : ¬(i = n),
    intro contra, rw contra at k_property, simp at k_property, 
    refine k_property,
    have i_property_2 : i < n, apply helper, refine hi, refine i_property,


    have k_property_2 : k_val_n < n, apply (helper2 i n k_val_n), tauto, tauto,

    refine _ ≫ (map (⟨i,i_property_2⟩+⟨k_val_n,k_property_2⟩)) ≫ _,
    apply eq_to_hom _,
    apply congr, refl, 

    simp, 
  

  },
  
  apply @recursion_on_lt (λ x y, (obj ⟨i,hi⟩ ⟶ obj ⟨j,hj⟩)),
  
  
  
  
  
  
  
  
  -- have H'' := classical.subtype_of_exists (exists_of_le H'),

  cases classical.subtype_of_exists (exists_of_le H') with w Hw,

  induction w, {
    simp at Hw, simp_rw Hw, refine 𝟙 _,
  },
  

  induction j, {
    induction i, refine 𝟙 _, 
    exfalso, apply nat.not_succ_le_zero, 
    
    -- have H : i_n.succ ≤ 0, induction f, induction f, refine f,
    refine H,
  },

  have H' : i ≤ j_n.succ, by tauto,
  have H'' := classical.subtype_of_exists (exists_of_le H'),
  
  -- I want do do cases H here, but I can't

  -- have H' := classical.dec H,



  -- refine (j_ih _ _) ≫ (map ⟨j_n, _⟩),
  -- apply lt_of_succ_lt_succ, refine hj,
  




end