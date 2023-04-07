import category_theory.functor
import logic.basic
open category_theory
-- equality of functors
-- nerve is a quasicategory
-- nerve has unique fillers
-- counit is an isomorphism

variables {C D : Type} [category C] [category D]
variables (F G : C ⥤ D)


structure functor_ext :=
(obj_ext : ∀ c : C, F.obj c = G.obj c)
(map_ext : ∀ a b : C, ∀ f : a ⟶ b, F.map f == G.map f)

lemma eq_of_heq_morphism {C : Type} [category C] {a a' b b' : C} 
    (p : a = a') (q : b = b')
    (f : a ⟶ b) (g : a' ⟶ b') (h : f == g) : q.rec_on (p.rec_on f) = g :=
begin
  apply eq_of_heq,
  have H := (eq_rec_heq p f),
  have : (q.rec_on f) == g,
  have H' := (eq_rec_heq q f),
  apply heq.trans, refine H', refine h,
  
  

  refine @heq.rec_on _ (p.rec_on f) (λ {β s}, q.rec_on s == g) _ f H,
  have Q := H.rec_on (Π s, (q.rec_on s) == g),
  
end
#check hext
-- lemma eq_of_heq_morphism {C : Type} [category C] {a a' b b' : C}
--         (p : (a ⟶ b) = (a' ⟶ b'))
--         (f : a ⟶ b) (g : a' ⟶ b') (h : f == g) : (p.mp f) = g :=
-- begin
--   unfold eq.mp,
-- end

lemma F_eq_G : (functor_ext F G) → F = G := begin

  intro H,
  cases F, cases G,

  simp, 
  destruct H, intros,
  split,
  
  funext, 
  refine (obj_ext x),
  
  
  

  
  
end