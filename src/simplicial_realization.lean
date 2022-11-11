import algebraic_topology.simplicial_object
import algebraic_topology.simplicial_set
import category_theory.path_category
import combinatorics.quiver.basic
import combinatorics.quiver.path

open sSet category_theory 
open category_theory.simplicial_object
open quiver

variable {X : sSet}

universe u

localized "notation (name := simplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.simplicial_object hole!).obj (opposite.op (simplex_category.mk n))"
  in simplicial

instance : (quiver (X _[0])) := by refine {
  hom := λ A B, {edge : X _[1] // X.δ 1 edge = A ∧ X.δ 0 edge = B}
}

def edge_to_hom (edge : X _[1]) : (X.δ 1 edge) ⟶ (X.δ 0 edge) := subtype.mk edge (by simp)

-- extract vertices of a 2-simplex
def v0 : (X _[2]) → (X _[0]) := X.δ 2 ≫ X.δ 1
def v1 : (X _[2]) → (X _[0]) := X.δ 2 ≫ X.δ 0
def v2 : (X _[2]) → (X _[0]) := X.δ 0 ≫ X.δ 0

-- type of 2-simplices with vertices A → B → C
def triangle (A B C : X _[0]) := {t : X _[2] // v0 t = A ∧ v1 t = B ∧ v2 t = C}

def δ0 {A B C : X _[0]} (t : triangle A B C) : B ⟶ C := begin
  destruct t, intros,

  have pB := and.left (and.right property),
  have pC := and.right (and.right property),

  have : v1 = (X.δ 0 ≫ X.δ 1) := @δ_comp_δ _ _ X _ 0 1 _,

  rw ← pB, rw ← pC, rw this, 

  exact (edge_to_hom (X.δ 0 val)), simp,
end

def δ1 {A B C : X _[0]} (t : triangle A B C) : A ⟶ C := begin
  destruct t, intros,

  have pA := and.left property,
  have pC := and.right (and.right property),
  
  have v0rw : v0 = (X.δ 1 ≫ X.δ 1) := @δ_comp_δ _ _ X _ 1 1 _,
  -- have v2rw : v2 = (X.δ 0 ≫ X.δ 1) := @δ_comp_δ _ _ X _ 0 1 _,

  rw ← pA, rw ← pC, rw v0rw,

  have edge := edge_to_hom (X.δ 1 val),
  have v2rw := @δ_comp_δ _ _ X _ 0 0 _,
  -- exact (edge_to_hom (X.δ 1 val)),
end

def δ2 {A B C : X _[0]} (t : triangle A B C) : A ⟶ B := begin
  
  destruct t, intros,

  have pA := and.left property,
  have pB := and.left (and.right property),

  rw ← pA, rw ← pB,

  exact (edge_to_hom (X.δ 2 val)),
end



def of_edge (edge : X _[1]) : path (X.δ 1 edge) (X.δ 0 edge) := hom.to_path $ edge_to_hom edge


inductive homotopic' {A B C : X _[0]} (p : A ⟶ C) (q : C ⟶ B) (r : A ⟶ B) : path A B → path A B → Prop
| homotopy (h : triangle A C B) (fp : δ2 h = p) : homotopic' (hom.to_path r) (path.comp (hom.to_path p) (hom.to_path q))

#check homotopic'.homotopy

inductive homotopic {A B : X _[0]} : path A B → path A B → Prop
| homotopy (h : X _[2])  

-- inductive homotopic : Π {A B : X _[0]} path A B → path A B → Prop
-- | homotopy (h : X _[2]) : homotopic (of_edge $ X.δ 1 h) (path.comp (of_edge $ X.δ 2 h)) (of_edge $ X.δ 0 h) 