import Mathlib.tactic

#check Eq 0 0


/- lemma lean_eq.symm {α : Sort u} {a b : α} (h : a = b) : b = a :=
begin
 apply eq.subst h,
 exact eq.refl a,
end

lemma lean_eq.symm2 {α : Sort u} {a b : α} (h : a = b) : b = a :=
begin
 induction h,
 exact eq.refl a,
end

lemma lean_eq.trans {α : Sort u} {a b c : α} (h1 : a = b) (h2 : b = c): a = c :=
begin
 induction h1,
 exact h2,
end -/

-- h.rec a

inductive my_Eq : α → α → Prop where
  | refl (a : α) : my_Eq a a

def my_Eq_subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b 
:= 
by
  show_term induction h₁
  exact h₂
  done

#print my_Eq_subst