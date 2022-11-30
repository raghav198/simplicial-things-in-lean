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
    (q : path (f ![0] a) (f ![0] b))
    (e : X _[1]) (ε : ends e b c) : path (f ![0] a) (f ![0] c) :=
path.cons q (subtype.mk (f ![1] e) (transport_ends f ε))

def map_edge {X Y : sSet} (f : X ⟶ Y) {a b : X _[0]} (e : a ⟶ b) : (f ![0] a) ⟶ (f ![0] b) :=
begin
  have ε : (ends e.val a b), destruct e, intros, subst a_1, simp, assumption,
  have H := transport_ends f ε,
  refine subtype.mk (f ![1] e) H,
end

def path_map {X Y : sSet} (f : X ⟶ Y) {a : X _[0]} : Π {b : X _[0]}, path a b → path (f ![0] a) (f ![0] b)
| _ path.nil := path.nil
| b (path.cons p q) := glue_one f (path_map p) q (begin 
  destruct q, intros, rw ← subtype.val_eq_coe, rw a_1, simp,
  dsimp [ends], 
  refine property,
end)

@[simp] lemma path_map_nil {X Y : sSet} {a : X _[0]} (f : X ⟶ Y) :
(@path_map X Y f a a path.nil) = path.nil := rfl

@[simp] lemma path_map_id {X : sSet} {a b} {p : path a b} : path_map (𝟙 X) p = p := begin
  induction p with b' c' p' e, simp, 
  unfold path_map, dsimp [glue_one], rw p_ih,
  destruct e, intros, subst a_1, simp,
end

@[simp] lemma path_map_app {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} (p : path a b) (q : path b c) :
  path_map f (p ** q) = ((path_map f p) ** (path_map f q)) :=
begin
  induction q, simp, 
  unfold path_map, unfold glue_one, simp, rw ← q_ih, 
  unfold path_map, unfold glue_one,
end

@[simp] lemma path_map_cons {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} {p : path a b} {e : b ⟶ c} :
  path_map f (path.cons p e) = (path_map f p).cons (map_edge f e) :=
begin
  unfold path_map, dsimp [glue_one], simp, dsimp [map_edge], refl,
end

@[simp] lemma path_map_comp {X Y Z : sSet} (f : X ⟶ Y) (g : Y ⟶ Z) {a b : X _[0]} {p : path a b} :
  path_map (f ≫ g) p = (@path_map Y Z g _ _ (@path_map X Y f _ _ p)) := begin

  induction p with b' c' p' e, simp,
  unfold path_map, dsimp [glue_one], rw p_ih, 
  simp, dsimp [map_edge], refl,
end

def fmap' {X Y : sSet} (f : X ⟶ Y) {a b : X _[0]} : 
path a b → ho_hom (f ![0] a) (f ![0] b) := λ p, ⟦path_map f p⟧

@[simp] lemma fmap'_comp {X Y : sSet} (f : X ⟶ Y) {a b c : X _[0]} (p : path a b) (q : path b c) :
  fmap' f (p ** q) = ho_comp (fmap' f p) (fmap' f q) := begin
  unfold fmap', simp, rw homotopy_compose,
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

def fmap {X Y : sSet} (f : X ⟶ Y) {a b : X _[0]} : ho_hom a b → ho_hom (f ![0] a) (f ![0] b) :=
quotient.lift (@fmap' X Y f a b) begin
  intros a1 b1 H,
  induction H,
  cases H_h with h C σ τ ρ, focus {
    apply quotient.sound,
    apply homotopic.lift,
    apply map_homotopy'',
    refine H_h,
  },
  refl,
  rw H_ih,
  rw H_ih_h1, rw H_ih_h2,
  simp, rw H_ih, 
  simp, rw H_ih,
end

@[simp] lemma id_of_fmap_id {X : sSet} {a b : X _[0]} :
  @fmap X X (𝟙 X) a b = id := begin
  ext, 
  have H := pick_rep x, revert H, rintros ⟨x, H⟩, subst H,
  dsimp [fmap], dsimp [fmap'], simp,
end

lemma fmap_id' {X Y : sSet} (f : X ⟶ Y) : Π (A : X _[0]), fmap f (𝟙 A) = 𝟙 (f ![0] A) := begin
  intro A,
  apply quotient.sound, simp,
end

lemma fmap_comp' {X Y : sSet} (f : X ⟶ Y) {A B C : X _[0]} {m1 : ho_hom A B} {m2 : ho_hom B C} :
  fmap f (ho_comp m1 m2) = ho_comp (fmap f m1) (fmap f m2) := begin
  have Hm1 := pick_rep m1, revert Hm1, rintro ⟨m1', m1'rw⟩, subst m1'rw,
  have Hm2 := pick_rep m2, revert Hm2, rintro ⟨m2', m2'rw⟩, subst m2'rw,
  rw homotopy_compose, 
  unfold fmap, simp,
end

def fmap_functor {X Y : sSet} (f : X ⟶ Y) : (X _[0]) ⥤ (Y _[0]) := {
  obj := λ A, f ![0] A,
  map := λ A B, fmap f,
  map_id' := fmap_id' f,
  map_comp' := λ A B C m1 m2, fmap_comp' f,
}

def HomotopyRealize : sSet ⥤ Cat := {
  obj := λ X, Cat.of(X _[0]),
  map := λ X Y, fmap_functor,
  map_id' := begin
    intro X, unfold fmap_functor, simp, 
    dsimp [id], congr,
  end,
  map_comp' := begin
    intros X Y Z f g,
    dsimp [fmap_functor], congr, simp,

    ext, 
    have H := pick_rep x_2, revert H, rintro ⟨x2', x2rw⟩, subst x2rw, 
    dsimp [fmap], dsimp [fmap'], 

    simp,
  end
}