import category_theory.category.basic
import tactic.omega
import tactic.linarith

open category_theory

namespace composable

universes u v
variables {C : Type u} [category.{v} C]

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

@[simp] lemma obj_0 {n : ℕ} {X Y : C} (fs : composable n X Y) : obj fs 0 = X := begin
  induction fs; tauto,
end

def drop : Π {n : ℕ} {X Y : C} (m : ℕ) (fs : composable n X Y), composable (n - m) (obj fs m) Y
| _ _ _ 0 fs := begin
  simp, refine fs,
end
| _ _ _ _ (composable.nil X) := begin
  simp, induction _x; simp, refine composable.nil X,
  
end

-- def slice : Π {n : ℕ} {X Y : C}, Π (fs : composable n X Y), 
--     Π (start : fin n), Π (len : fin (n + 1 - start)), composable len (obj fs start) (obj fs (start + len))
-- | _ _ _ (composable.hom X Y f) ⟨a, Ha⟩ ⟨b, Hb⟩ := begin
--   simp, 
--   simp at Ha, subst Ha, simp at Hb,
--   dsimp [obj],
-- end


-- def drop : Π {n : ℕ} {X Y : C}, Π (m : fin n), Π (fs : composable n X Y), composable (n - m) (obj fs m) Y
-- | _ _ _ ⟨0, _⟩ fs := begin
--   simp, refine fs,
-- end
-- | _ _ _ ⟨m+1, H⟩ (composable.hom X Y f) := begin
--   simp, dsimp [obj], exfalso, linarith,
-- end
-- | _ _ _ ⟨m+1, H⟩ (composable.cons X Y Z f gs) := begin
--   simp,
--   refine drop ⟨m, _⟩ gs, omega,
-- end


-- def take : Π {n : ℕ} {X Y : C}, Π (m : fin n), Π (fs : composable n X Y), composable m X (obj fs m)


end composable