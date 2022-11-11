import algebraic_topology.simplicial_set

variable (X : sSet)

universe u

localized "notation (name := simplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.simplicial_object hole!).obj (opposite.op (simplex_category.mk n))"
  in simplicial

def edge_to_hom (edge : X _[1]) : (X.δ 1 edge) ⟶ (X.δ 0 edge) := subtype.mk edge (by simp)

-- extract vertices of a 2-simplex
def v0 : (X _[2]) → (X _[0]) := X.δ 2 ≫ X.δ 1
def v1 : (X _[2]) → (X _[0]) := X.δ 2 ≫ X.δ 0
def v2 : (X _[2]) → (X _[0]) := X.δ 0 ≫ X.δ 0

-- type of 2-simplices with vertices A → B → C
def triangle (A B C : X _[0]) := {t : X _[2] // v0 t = A ∧ v1 t = B ∧ v2 t = C}

def δ0 {A B C : X _[0]} (t : triangle A B C) : B ⟶ C := begin
  destruct t, intros,

  have pA := and.left property,
  have pB := and.left (and.right property),
  have pC := and.right (and.right property),

  have : v1 = (X.δ 0 ≫ X.δ 1) := @δ_comp_δ _ _ X _ 0 1 _,

  rw ← pB, rw ← pC, rw this, 

  exact (edge_to_hom (X.δ 0 val)), simp,
end

def δ1 {A B C : X _[0]} (t : triangle A B C) : A ⟶ C := begin
  destruct t, intros,

  have pA := and.left property,
  have pB := and.left (and.right property),
  have pC := and.right (and.right property),

  rw ← pA, rw ← pC,

  exact (edge_to_hom (X.δ 1 val)),
end

def δ2 {A B C : X _[0]} (t : triangle A B C) : A ⟶ B := begin
  
  destruct t, intros,

  have pA := and.left property,
  have pB := and.left (and.right property),
  have pC := and.right (and.right property),

  rw ← pA, rw ← pB,

  exact (edge_to_hom (X.δ 2 val)),
end
