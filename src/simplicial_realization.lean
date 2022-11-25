import algebraic_topology.simplicial_set
import path_homotopy
import combinatorics.quiver.basic
import combinatorics.quiver.path

open quiver category_theory

variable {X : sSet}

-- variables (A B C : X _[0])

instance path.is_setoid (A B : X _[0]) : setoid (path A B) := by refine {
  r := homotopic A B,
  iseqv := htpy_is_equiv A B
}

def my_prod (α β : Type*) := α×β

def ho_hom (A B : X _[0]) := quotient (path.is_setoid A B)
def ho_hom_pair (A B C : X _[0]) := quotient (setoid.prod (path.is_setoid A B) (path.is_setoid B C))
def ho_id (A : X _[0]) : ho_hom A A := ⟦@path.nil _ _ A⟧

def uncurry {α β γ : Type*} (f : α → β → γ) : α × β → γ := λ x, f x.fst x.snd 

def comp_ho' {A B C : X _[0]} (f : path A B) (g : path B C) : ho_hom A C := ⟦f.comp g⟧

def ho_comp {A B C : X _[0]} : ho_hom A B → ho_hom B C → ho_hom A C :=
quotient.lift₂ comp_ho' (begin
  intros a1 a2 b1 b2 H1 H2, apply quotient.sound, 
  apply homotopic.lift, apply homotopic'.trans,
  
  apply homotopic.comp_l, refine H2,
  apply homotopic.comp_r, refine H1,
end)

-- pick a representative using ⟦notation⟧
lemma pick_rep {A B : X _[0]} (f : ho_hom A B) : ∃ (f' : path A B), ⟦f'⟧ = f := quot.exists_rep f

lemma homotopy_compose {A B C : X _[0]} (f : path A B) (g : path B C) : 
ho_comp ⟦f⟧ ⟦g⟧ = ⟦f.comp g⟧ := begin
  apply quotient.sound, refl,
end

instance : category (X _[0]) := by refine {
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
