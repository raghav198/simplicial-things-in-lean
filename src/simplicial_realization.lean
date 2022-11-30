import algebraic_topology.simplicial_object
import algebraic_topology.simplicial_set
import path_homotopy
import combinatorics.quiver.basic
import combinatorics.quiver.path

open quiver category_theory
open category_theory.simplicial_object

universe u

variable {X : sSet.{u}}

instance path.is_setoid (A B : X _[0]) : setoid (path A B) := by refine {
  r := homotopic A B,
  iseqv := htpy_is_equiv A B
}

def ho_hom (A B : X _[0]) := quotient (path.is_setoid A B)
def ho_id (A : X _[0]) : ho_hom A A := ⟦@path.nil _ _ A⟧

def ho_comp' {A B C : X _[0]} (f : path A B) (g : path B C) : ho_hom A C := ⟦f.comp g⟧

def ho_comp {A B C : X _[0]} : ho_hom A B → ho_hom B C → ho_hom A C :=
quotient.lift₂ ho_comp' (begin
  intros a1 a2 b1 b2 H1 H2, apply quotient.sound, 
  apply homotopic.trans,
  
  apply homotopic.comp_l, refine H2,
  apply homotopic.comp_r, refine H1,
end)

-- pick a representative using ⟦notation⟧
lemma pick_rep {A B : X _[0]} (f : ho_hom A B) : ∃ (f' : path A B), ⟦f'⟧ = f := quot.exists_rep f

lemma homotopy_compose {A B C : X _[0]} (f : path A B) (g : path B C) : 
ho_comp ⟦f⟧ ⟦g⟧ = ⟦f.comp g⟧ := begin
  apply quotient.sound, refl,
end

instance realized : category (X _[0]) := by refine {
  hom := ho_hom,
  id := ho_id,
  comp := λ A B C : X _[0], λ f : ho_hom A B, λ g : ho_hom B C, ho_comp f g,

  id_comp' := begin
    intros, dsimp, 
    
    unfold ho_id, 
    have H := pick_rep f, revert H, rintro ⟨f', frw⟩, subst frw, 
    rw homotopy_compose, simp,
  end,

  comp_id' := begin
    intros, dsimp, unfold ho_id, 
    
    have H := pick_rep f, revert H, rintro ⟨f', frw⟩, subst frw, 
    rw homotopy_compose, simp,
  end,

  assoc' := begin
    intros, dsimp,

    have H := pick_rep f, revert H, rintro ⟨f', frw⟩, subst frw, 
    have H := pick_rep g, revert H, rintro ⟨g', grw⟩, subst grw,
    have H := pick_rep h, revert H, rintro ⟨h', hrw⟩, subst hrw, 

    repeat {rw homotopy_compose},
    rw path.comp_assoc,
  end,
}

notation (name := simplicial_map.at) f ` ![`:1000 n `]` :=
  (f : category_theory.nat_trans hole! hole!).app (opposite.op (simplex_category.mk n))


lemma simplicial_map_preserves_faces {X Y : sSet} (f : X ⟶ Y) {n : ℕ} {i : fin (n+2)} {σ : X _[n+1] } :
  Y.δ i (f ![n+1] σ) = f ![n] (X.δ i σ) := begin
   have H := congr_fun (f.naturality (@simplex_category.δ n i).op) σ,
   simp at H,
   have : X.δ i = X.map (@simplex_category.δ n i).op, dsimp [δ], refl,
   rw this, clear this,
   have : Y.δ i = Y.map (@simplex_category.δ n i).op, dsimp [δ], refl,
   rw this, clear this,
   rw H,
end

def transport_ends {X Y : sSet} {a b : X _[0]} {ab : X _[1]}
  (f : X ⟶ Y) (e : ends ab a b) : ends (f ![1] ab) (f ![0] a) (f ![0] b) := begin
    destruct e, intros, subst left, subst right, split, 
    repeat {refine simplicial_map_preserves_faces _},
end

def glue_one {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} 
    (p : path a b) (q : path (f ![0] a) (f ![0] b))
    (e : X _[1]) (ε : ends e b c) : path (f ![0] a) (f ![0] c) :=
path.cons q (subtype.mk (f ![1] e) (transport_ends f ε))


def path_map {X Y : sSet} (f : X ⟶ Y) {a : X _[0]} : Π {b : X _[0]}, path a b → path (f ![0] a) (f ![0] b)
| _ path.nil := path.nil
| b (path.cons p q) := glue_one f p (path_map p) q (begin 
  destruct q, intros, rw ← subtype.val_eq_coe, rw a_1, simp,
  dsimp [ends], 
  refine property,
end)

@[simp] lemma path_map_nil {X Y : sSet} {a : X _[0]} (f : X ⟶ Y) :
(@path_map X Y f a a path.nil) = path.nil := rfl

def fmap' {X Y : sSet} (f : X ⟶ Y) {a b : X _[0]} : 
path a b → ho_hom (f ![0] a) (f ![0] b) := λ p, ⟦path_map f p⟧

@[simp] lemma path_map_comp {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} (p : path a b) (q : path b c) :
  path_map f (p ** q) = ((path_map f p) ** (path_map f q)) :=
begin
  induction q, simp, 
  unfold path_map, unfold glue_one, simp, rw ← q_ih, 
  unfold path_map, unfold glue_one,
end

@[simp] lemma fmap'_comp {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} (p : path a b) (q : path b c) :
  fmap' f (p ** q) = ho_comp (fmap' f p) (fmap' f q) := begin
  unfold fmap', simp, rw homotopy_compose,
end

lemma edge_path_map_transport_ends {X Y : sSet} {a b : X _[0]} {ab : X _[1]} 
    (e : ends ab a b) (f : X ⟶ Y) : 
  path_map f (to_path e) = to_path (transport_ends f e) :=
begin
  unfold to_path, unfold edge_to_path, unfold edge_to_hom, --unfold hom.to_path,
  unfold path_map, unfold glue_one, simp,
end

lemma map_homotopy'' {X Y : sSet} {a b : X _[0]} {p q : path a b} (f : X ⟶ Y) :
  (homotopic'' a b p q) → (homotopic'' (f ![0] a) (f ![0] b) (path_map f p) (path_map f q)) := begin

    intros H, cases H,
    unfold path_map, unfold glue_one, simp,
    simp_rw ← simplicial_map_preserves_faces, 

    have fσ : Y.δ 1 (Y.δ 1 (f ![2] H_h)) = f ![0] a,
    subst H_σ, repeat {rw (simplicial_map_preserves_faces f)},

    have fτ : Y.δ 0 (Y.δ 1 (f ![2] H_h)) = f ![0] b,
    subst H_τ, repeat {rw (simplicial_map_preserves_faces f)},

    have fρ : Y.δ 0 (Y.δ 2 (f ![2] H_h)) = f ![0] H_C,
    subst H_ρ, repeat {rw (simplicial_map_preserves_faces f)},

    have H' := homotopic''.homotopy (f ![2] H_h) fσ fτ fρ,

    dsimp [edge_to_path] at *, dsimp [edge_to_hom] at *,
    unfold path_map, unfold glue_one, simp,
    simp_rw ← simplicial_map_preserves_faces,
    refine H',
end

def fmap {X Y : sSet} (f : X ⟶ Y) {a b : X _[0]} := quotient.lift (@fmap' X Y f a b) begin
  intros a1 b1 H,
  induction H,
  cases H_h with h C σ τ ρ, focus {
    apply quotient.sound,
    apply homotopic.lift, --apply homotopic'.lift, 
    apply map_homotopy'',
    refine H_h,
  },
  refl,
  rw H_ih,
  rw H_ih_h1, rw H_ih_h2,
  simp, rw H_ih, 
  simp, rw H_ih,
end
