import algebraic_topology.simplicial_object
import algebraic_topology.simplicial_set
import category_theory.functor.basic
import combinatorics.quiver.basic
import combinatorics.quiver.path

open sSet quiver category_theory
open category_theory.simplicial_object
open category_theory.functor

variable {X : sSet}

notation (name := simplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.simplicial_object hole!).obj (opposite.op (simplex_category.mk n))


instance : quiver (X _[0]) := by refine {
  hom := λ A B, {edge : X _[1] // X.δ 1 edge = A ∧ X.δ 0 edge = B}
}

def edge_to_hom (edge : X _[1]) (A B : X _[0]) (σ : X.δ 1 edge = A) (τ : X.δ 0 edge = B) : 
A ⟶ B := subtype.mk edge (by split; assumption)

def edge_to_path (edge : X _[1]) (A B : X _[0]) (σ : X.δ 1 edge = A) (τ : X.δ 0 edge = B) :
path A B := hom.to_path (edge_to_hom edge A B σ τ)


lemma comp_of_app {n} {v : X _[n+2]} {i : fin(n+2)} {j : fin(n+3)} : X.δ i (X.δ j v) = (X.δ j ≫ X.δ i) v := by simp

lemma simplicial_11 (h : X _[2]) : X.δ 1 (X.δ 1 h) = X.δ 1 (X.δ 2 h) := begin
  repeat {rw comp_of_app},

  have H := @δ_comp_δ_self _ _ X 0 1,
  simp at H, rw H,
end

lemma simplicial_10 (h : X _[2]) : X.δ 1 (X.δ 0 h) = X.δ 0 (X.δ 2 h) := begin
  repeat {rw comp_of_app},

  have H := @δ_comp_δ _ _ X 0 0 1, simp at H, rw ← H,
end

lemma simplicial_00 (h : X _[2]) : X.δ 0 (X.δ 0 h) = X.δ 0 (X.δ 1 h) := begin
  repeat {rw comp_of_app},

  have H := @δ_comp_δ_self _ _ X 0 0,
  simp at H, rw H,
end


inductive homotopic'' (A B : X _[0]) : path A B → path A B → Prop
| homotopy (h : X _[2]) {C : X _[0]} 
            (σ : X.δ 1 (X.δ 1 h) = A) 
            (τ : X.δ 0 (X.δ 1 h) = B)
            (ρ : X.δ 0 (X.δ 2 h) = C) : 
        homotopic'' (edge_to_path (X.δ 1 h) A B σ τ) 
                  (path.comp 
                    (edge_to_path (X.δ 2 h) A C ((simplicial_11 h).symm.trans σ)  ρ) 
                    (edge_to_path (X.δ 0 h) C B ((simplicial_10 h).trans ρ) ((simplicial_00 h).trans τ)))


mutual inductive homotopic', homotopic
with homotopic' : Π (A B : X _[0]), path A B → path A B → Prop
| lift (A B : X _[0]) (p q : path A B) (h : homotopic'' A B p q) : homotopic' A B p q
| refl (A B : X _[0]) (p : path A B) : homotopic' A B p p
| symm (A B : X _[0]) (p q : path A B) (h : homotopic A B p q) : homotopic' A B q p
| trans (A B : X _[0]) (p q r : path A B) (h1 : homotopic A B p q) (h2 : homotopic A B q r) : homotopic' A B p r
with homotopic : Π (A B : X _[0]), path A B → path A B → Prop
| lift (A B : X _[0]) (p q : path A B) (h : homotopic' A B p q) : homotopic A B p q
| comp_l (A B : X _[0]) {C : X _[0]} (p : path A C) (q r : path C B) (h : homotopic C B q r) : homotopic A B (p.comp q) (p.comp r)
| comp_r (A B : X _[0]) {C : X _[0]} (p q : path A C) (r : path C B) (h : homotopic A C p q) : homotopic A B (p.comp r) (q.comp r)

@[refl] lemma htpy_refl (A B : X _[0]) (p : path A B) : 
homotopic A B p p := homotopic.lift A B p p (homotopic'.refl A B p)

@[symm] lemma htpy_symm (A B : X _[0]) (p q : path A B) : 
homotopic A B p q → homotopic A B q p :=
λ h, homotopic.lift A B q p (homotopic'.symm A B p q h)

@[trans] lemma htpy_trans (A B : X _[0]) (p q r : path A B) :
homotopic A B p q → homotopic A B q r → homotopic A B p r :=
λ h1, λ h2, homotopic.lift A B p r (homotopic'.trans A B p q r h1 h2)

theorem htpy_is_equiv (A B : X _[0]) : equivalence (homotopic A B) := 
mk_equivalence (homotopic A B) (htpy_refl A B) (htpy_symm A B) (htpy_trans A B)
