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
#eval let l := [1, 2]; l[3]!
#check getElem!
#check GetElem
#check getElem!_def

inductive HasType : Ctxt → Term → Ty → Prop where
| var (h : n < Γ.length) : HasType Γ (var n) (Γ[n])
| app : HasType Γ t (A ⟶ B) → HasType Γ u A → HasType Γ (app t u) B
| lam : HasType (A :: Γ) t B → HasType Γ (lam t) (A ⟶ B)
| zero : HasType Γ zero nat
| succ : HasType Γ t nat → HasType Γ (succ t) nat
| rect : HasType Γ z A → HasType Γ s (nat ⟶ A ⟶ A) → HasType Γ t nat → HasType Γ (rect z s t) A

inductive Renaming where
| idRen : Renaming
| shift : Renaming
| cons₀ : Renaming → Renaming
| comp : Renaming → Renaming → Renaming

def liftRen (τ : Renaming) : Renaming := .cons₀ (τ.comp .shift)


def renVar (k : Nat) (ren : Renaming) : Nat :=
match ren with
| .idRen => k
| .shift => k+1
| .cons₀ τ => if k = 0 then 0 else renVar (k-1) τ
| .comp τ ρ => renVar (renVar k τ) ρ

def substRen (t : Term) (τ : Renaming) : Term :=
match t with
| var k => var (renVar k τ)
| app t u => app (substRen t τ) (substRen u τ)
| lam t => lam (substRen t (liftRen τ))
| zero => zero
| succ t => succ (substRen t τ)
| rect z s t => rect (substRen z τ) (substRen s τ) (substRen t τ)

inductive Substitution where
| ren : Renaming → Substitution
| cons : Term → Substitution → Substitution
| comp : Substitution → Renaming → Substitution

def lift (σ : Substitution) : Substitution := .cons (var 0) (σ.comp .shift)

def substVar (k : Nat) (σ : Substitution) : Term :=
match σ with
| .ren τ => var <| renVar k τ
| .cons t σ => if k = 0 then t else substVar (k-1) σ
| .comp σ τ => substRen (substVar k σ) τ

def subst (t : Term) (σ : Substitution) : Term :=
match t with
| var k => substVar k σ
| app t₁ t₂ => app (subst t₁ σ) (subst t₂ σ)
| lam t' => lam (subst t' (lift σ))
| zero => zero
| succ t' => succ (subst t' σ)
| rect z s t' => rect (subst z σ) (subst s σ) (subst t' σ)

infix:30 "∘" => Substitution.comp
notation "id" => (Substitution.ren Renaming.idRen)
infixr:30 "⋆" => Substitution.cons

notation t "[" σ "]" => subst t σ
notation t "[" u "]" => subst t (u⋆id)
prefix:max "⇑" => lift

#eval (var 0) [ lam (var 3) ]
#eval subst (var 0) (zero ⋆ zero.succ ⋆ zero.succ.succ ⋆ id)
#eval subst (var 1) (zero ⋆ zero.succ ⋆ zero.succ.succ ⋆ id)

#check ⇑id
#eval subst (var 1) ⇑(zero ⋆ id)

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

inductive CompEnv : List Ty → Substitution → Prop where
| empty : CompEnv [] id
| cons : Comp ty t → CompEnv tys σ → CompEnv (ty :: tys) (t ⋆ σ)

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

theorem WHNorm.succ {t t' : Term}
  : WHNorm t t' → WHNorm t.succ t'.succ := by
  intros h
  induction h; apply WHNorm.refl
  case _ t₁ t₂ t₃ _ _ _ =>
    apply WHNorm.step (t' := t₂.succ) <;> grind [WHRed]


theorem subst_lift {t v : Term} {σ : Substitution} :
  (t[⇑σ])[v] = t [v ⋆ σ] := by
  sorry

theorem comp_ty
        (typed : HasType Γ t ty)
        (compEnv : CompEnv Γ σ)
        : Comp ty (t[σ]) := by
  revert compEnv σ
  induction typed
  case _ n Γ h =>
    sorry
  case _ t _ _ u ty₁ ty₂ ih₁ ih₂ =>
    intros σ compEnv
    simp [Comp] at ih₁
    have ⟨v_fun, ⟨h₁, h₁'⟩⟩ := ih₁ compEnv
    have ih₂ := ih₂ compEnv
    cases h₁'
    case vallam A B comp_u t' comp_t' =>
    simp [subst]
    apply comp_exp (v := (t'.lam).app ((subst u σ)))
    . apply comp_exp (v := t'[subst u σ])
      . grind
      . apply WHNorm.appLam
    . apply WHNorm.appNe
      exact h₁
  case _ t _ _ ih  =>
    simp [Comp, subst]
    intros σ compEnv
    exists (t[⇑σ]).lam
    constructor; constructor
    constructor
    intros
    rw [subst_lift]
    apply ih
    constructor <;> grind
  case _ =>
    simp [subst]
    intros; exists .zero; grind [ValNat, WHNorm]
  case _ Γ t ty ih =>
    simp [subst]
    intros σ compEnv; simp [Comp]
    have ⟨v, h⟩ := ih compEnv
    exists v.succ
    constructor
    . apply WHNorm.succ <;> grind
    . grind [ValNat]
  case _ => sorry
