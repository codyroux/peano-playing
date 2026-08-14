import Init.Grind.Tactics


inductive Term where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term
| zero : Term
| succ : Term → Term
| rect : Term → Term → Term → Term

inductive Ty where
| nat : Ty
| arrow : Ty → Ty → Ty

infixr:30 " ⟶ " => Ty.arrow

abbrev Ctxt := List Ty

open Term Ty

#check ((nat ⟶ nat) ⟶ nat)

#check (nat ⟶ (nat ⟶ nat))

#check List.get

def List.getLt (l : List α) (n : Nat) (h : n < l.length) : α :=
match n, l with
| 0, A::_ => A
| n+1, A::l => List.getLt l n (by simp at h; omega)

inductive HasType : Ctxt → Term → Ty → Prop where
| var (h : n < Γ.length) : HasType Γ (var n) (Γ.getLt n h)
| app : HasType Γ t (A ⟶ B) → HasType Γ u A → HasType Γ (app t u) B
| lam : HasType (A :: Γ) t B → HasType Γ (lam t) (A ⟶ B)
| zero : HasType Γ zero nat
| succ : HasType Γ t nat → HasType Γ (succ n) nat
| rect : HasType Γ z A → HasType Γ s (nat ⟶ A ⟶ A) → HasType Γ t nat → HasType Γ (rect z s t) A

def subst (n : Nat) (t u : Term) : Term :=
match t with
| var k => if n = k then u else t
| (app t₁ t₂) => app (subst n t₁ u) (subst n t₂ u)
| lam t' => lam (subst (n+1) t' u)
| zero => zero
| succ t' => succ (subst n t' u)
| rect z s t' => rect (subst n z u) (subst n s u) (subst n t' u)

def substList (n : Nat) (t : Term) (us : List Term) : Term :=
match t with
| var k => if h:n+k < us.length then us.getLt (n+k) h else t
| (app t₁ t₂) => app (substList n t₁ us) (substList n t₂ us)
| lam t' => lam (substList (n+1) t' us)
| zero => zero
| succ t' => succ (substList n t' us)
| rect z s t' => rect (substList n z us) (substList n s us) (substList n t' us)


notation t "[" u "]" => subst 0 t u

#eval (var 0) [ lam (var 3) ]

-- small step :(
inductive WHRed : Term → Term → Prop where
| appNe : WHRed t t' → WHRed (app t u) (app t' u)
| appLam : WHRed (app (lam t) u) (t [u])
| rectNe : WHRed t t' → WHRed (rect z s t) (rect z s t')
| succ : WHRed t t' → WHRed (succ t) (succ t') -- it kind of sucks to have this one, but it makes defining computability a bit easier.
| rectz : WHRed (rect z s zero) z
| rects : WHRed (rect z s (succ t)) (app (app s t) (rect z s t))

-- This is somehwere in the stdlib whatever
inductive WHNorm : Term → Term → Prop where
| refl : WHNorm t t
| step : WHRed t t' → WHNorm t' t'' → WHNorm t t''

theorem WHNorm.trans
(h₁ : WHNorm t t')
(h₂ : WHNorm t' t'')
: WHNorm t t'' := by induction h₁ <;> grind [WHNorm]

-- It'd be nicer to define these mutually
inductive ValNat : Term → Prop
| valzero : ValNat zero
| valSucc : ValNat k → ValNat (succ k)

inductive ValArrow (Comp₁ Comp₂ : Term → Prop) : Term → Prop
| vallam : (∀ v, Comp₁ v → Comp₂ (t[v])) →
               ValArrow Comp₁ Comp₂ (lam t)

def Comp (ty : Ty) (t : Term) : Prop :=
match ty with
| nat => ∃ v, WHNorm t v ∧ ValNat v
| ty₁ ⟶ ty₂ => ∃ v, WHNorm t v ∧ ValArrow (Comp ty₁) (Comp ty₂) v

infix:30 "⊩" => (fun t ty => Comp ty t)

#check zero ⊩ nat

inductive CompEnv : List Ty → List Term → Prop where
| empty : CompEnv [] []
| cons : Comp ty t → CompEnv tys ts → CompEnv (ty :: tys) (t :: ts)

theorem compenv_len (h : CompEnv Γ vs) : Γ.length = vs.length := by
  cases h
  case _ => grind
  case _ => simp; apply compenv_len; trivial

theorem compenv_getLen
  (h : n < Γ.length)
  (h' : n < vs.length)
  (compenv : CompEnv Γ vs) : Comp (Γ.getLt n h) (vs.getLt n h') := by
  cases compenv; grind
  cases n <;> simp [List.getLt]; grind
  apply compenv_getLen <;> grind

theorem comp_val_nat
  (val : ValNat v)
  : Comp nat v := by
  simp [Comp]
  exists v
  grind [WHNorm]

theorem comp_val_arr
  (val : ValArrow (Comp ty₁) (Comp ty₂) v)
  : Comp (ty₁ ⟶ ty₂) v := by
  simp [Comp]
  exists v; grind [WHNorm]

theorem comp_exp
  (h₁ : Comp A v)
  (h₂ : WHNorm t v)
  : Comp A t := by
  cases A <;> simp [Comp] at *
  . have ⟨v', _⟩ := h₁
    exists v'
    refine ⟨?_, by grind⟩
    apply WHNorm.trans
    . exact h₂
    . grind
  . have ⟨v', _⟩ := h₁
    exists v'
    refine ⟨?_, by grind⟩
    apply WHNorm.trans
    . exact h₂
    . grind

-- and the others...
theorem WHNorm.appNe
  (h : WHNorm t t')
  : WHNorm (t.app u) (t'.app u) := by
  induction h
  . grind [WHNorm]
  . apply WHNorm.step
    . apply WHRed.appNe
      trivial
    . trivial

theorem WHNorm.appLam {t u : Term}
  : WHNorm (t.lam.app u) (t[u]) := by
  apply WHNorm.step
  . apply WHRed.appLam
  . apply WHNorm.refl


theorem comp_ty
        (typed : HasType Γ t ty)
        (compEnv : CompEnv Γ vs)
        : Comp ty (substList 0 t vs) := by
  revert compEnv
  induction typed
  case _ n h =>
    intro compEnv
    simp [substList]
    have h' := compenv_len compEnv; split <;> try grind
    apply compenv_getLen; grind
  case _ t _ _ u ty₁ ty₂ ih₁ ih₂ =>
    intros compEnv
    simp [Comp] at ih₁
    have ⟨v_fun, ⟨h₁, h₁'⟩⟩ := ih₁ compEnv
    have ih₂ := ih₂ compEnv
    cases h₁'
    case vallam A B comp_u t' comp_t' =>
    simp [substList]
    apply comp_exp (v := (t'.lam).app ((substList 0 u vs)))
    . apply comp_exp (v := t'[substList 0 u vs])
      . grind
      . apply WHNorm.appLam
    . apply WHNorm.appNe
      exact h₁
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
