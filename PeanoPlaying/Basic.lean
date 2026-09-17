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

theorem ren_congr (t : Term) :
    ∀ τ₁ τ₂ : Renaming, (∀ k, renVar k τ₁ = renVar k τ₂) → substRen t τ₁ = substRen t τ₂ := by
  induction t with
  | var k => intro τ₁ τ₂ h; simp [substRen, h k]
  | app t u iht ihu => intro τ₁ τ₂ h; simp [substRen, iht τ₁ τ₂ h, ihu τ₁ τ₂ h]
  | lam t iht =>
    intro τ₁ τ₂ h
    simp only [substRen]
    congr 1
    apply iht
    intro k
    cases k with
    | zero => simp [liftRen, renVar]
    | succ k => simp [liftRen, renVar, h k]
  | zero => intro τ₁ τ₂ h; simp [substRen]
  | succ t iht => intro τ₁ τ₂ h; simp [substRen, iht τ₁ τ₂ h]
  | rect z s t ihz ihs iht => intro τ₁ τ₂ h; simp [substRen, ihz τ₁ τ₂ h, ihs τ₁ τ₂ h, iht τ₁ τ₂ h]

theorem subst_congr (t : Term) :
    ∀ σ₁ σ₂ : Substitution, (∀ k, substVar k σ₁ = substVar k σ₂) → subst t σ₁ = subst t σ₂ := by
  induction t with
  | var k => intro σ₁ σ₂ h; simp [subst, h k]
  | app t u iht ihu => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h, ihu σ₁ σ₂ h]
  | lam t iht =>
    intro σ₁ σ₂ h
    simp only [subst]
    congr 1
    apply iht
    intro k
    cases k with
    | zero => simp [lift, substVar]
    | succ k => simp [lift, substVar, h k]
  | zero => intro σ₁ σ₂ h; simp [subst]
  | succ t iht => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h]
  | rect z s t ihz ihs iht => intro σ₁ σ₂ h; simp [subst, ihz σ₁ σ₂ h, ihs σ₁ σ₂ h, iht σ₁ σ₂ h]

theorem substRen_comp (t : Term) :
    ∀ τ₁ τ₂ : Renaming, substRen (substRen t τ₁) τ₂ = substRen t (τ₁.comp τ₂) := by
  induction t with
  | var k => intro τ₁ τ₂; simp [substRen, renVar]
  | app t u iht ihu => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂, ihu τ₁ τ₂]
  | lam t iht =>
    intro τ₁ τ₂
    simp only [substRen]
    congr 1
    rw [iht (liftRen τ₁) (liftRen τ₂)]
    apply ren_congr
    intro k
    cases k with
    | zero => simp [liftRen, renVar]
    | succ k => simp [liftRen, renVar]
  | zero => intro τ₁ τ₂; simp [substRen]
  | succ t iht => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂]
  | rect z s t ihz ihs iht => intro τ₁ τ₂; simp [substRen, ihz τ₁ τ₂, ihs τ₁ τ₂, iht τ₁ τ₂]

theorem subst_ren_fuse (t : Term) :
    ∀ (ρ : Substitution) (τ : Renaming), subst t (ρ.comp τ) = substRen (subst t ρ) τ := by
  induction t with
  | var k => intro ρ τ; simp [subst, substVar]
  | app t u iht ihu => intro ρ τ; simp [subst, substRen, iht ρ τ, ihu ρ τ]
  | lam t iht =>
    intro ρ τ
    simp only [subst, substRen]
    congr 1
    rw [← iht (lift ρ) (liftRen τ)]
    apply subst_congr
    intro k
    cases k with
    | zero => simp [lift, substVar, substRen, liftRen, renVar]
    | succ k =>
      simp only [lift, substVar, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      rw [substRen_comp, substRen_comp]
      apply ren_congr
      intro m
      simp [renVar, liftRen]
  | zero => intro ρ τ; simp [subst, substRen]
  | succ t iht => intro ρ τ; simp [subst, substRen, iht ρ τ]
  | rect z s t ihz ihs iht => intro ρ τ; simp [subst, substRen, ihz ρ τ, ihs ρ τ, iht ρ τ]

theorem ren_subst_fuse (t : Term) :
    ∀ (τ : Renaming) (ρ σ : Substitution),
      (∀ k, substVar (renVar k τ) ρ = substVar k σ) →
      subst (substRen t τ) ρ = subst t σ := by
  induction t with
  | var k => intro τ ρ σ h; simp [substRen, subst, h k]
  | app t u iht ihu => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h, ihu τ ρ σ h]
  | lam t iht =>
    intro τ ρ σ h
    simp only [substRen, subst]
    congr 1
    apply iht
    intro k
    cases k with
    | zero => simp [liftRen, renVar, lift, substVar]
    | succ k => simp [liftRen, renVar, lift, substVar, h k]
  | zero => intro τ ρ σ h; simp [substRen, subst]
  | succ t iht => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h]
  | rect z s t ihz ihs iht => intro τ ρ σ h; simp [substRen, subst, ihz τ ρ σ h, ihs τ ρ σ h, iht τ ρ σ h]

theorem subst_id (t : Term) : t [id] = t := by
  induction t with
  | var k => simp [subst, substVar, renVar]
  | app t u iht ihu => simp [subst, iht, ihu]
  | lam t iht =>
    simp only [subst]
    congr 1
    rw [subst_congr t (⇑ id) id (by intro k; cases k <;> simp [lift, substVar, substRen, renVar])]
    exact iht
  | zero => simp [subst]
  | succ t iht => simp [subst, iht]
  | rect z s t ihz ihs iht => simp [subst, ihz, ihs, iht]

theorem subsRen_shift_cons :
  (substRen t Renaming.shift) [v ⋆ σ] = t [σ] := by
  apply ren_subst_fuse
  intro k
  simp [renVar, substVar]

theorem substVar_lift {x : Nat} {v : Term} {σ : Substitution} :
  (substVar x (⇑ σ)) [v] = substVar x (v ⋆ σ) := by
  cases x with
  | zero => simp [substVar, lift, subst]
  | succ x =>
    simp only [lift, substVar, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    rw [subsRen_shift_cons]
    exact subst_id _

theorem subst_fuse (t : Term) :
    ∀ (ρ₁ ρ₂ σ : Substitution),
      (∀ k, (substVar k ρ₁) [ρ₂] = substVar k σ) →
      (t [ρ₁]) [ρ₂] = t [σ] := by
  induction t with
  | var k => intro ρ₁ ρ₂ σ h; simp [subst, h k]
  | app t u iht ihu => intro ρ₁ ρ₂ σ h; simp [subst, iht ρ₁ ρ₂ σ h, ihu ρ₁ ρ₂ σ h]
  | lam t iht =>
    intro ρ₁ ρ₂ σ h
    simp only [subst]
    congr 1
    apply iht
    intro k
    cases k with
    | zero => simp [lift, substVar, subst]
    | succ k =>
      have e1 : substVar (k+1) (⇑ ρ₁) = substRen (substVar k ρ₁) Renaming.shift := by
        simp [lift, substVar]
      have e2 : substVar (k+1) (⇑ σ) = substRen (substVar k σ) Renaming.shift := by
        simp [lift, substVar]
      rw [e1, e2]
      rw [ren_subst_fuse (substVar k ρ₁) Renaming.shift (⇑ ρ₂) (ρ₂.comp Renaming.shift)
            (by intro m; simp [lift, substVar, renVar])]
      rw [subst_ren_fuse (substVar k ρ₁) ρ₂ Renaming.shift]
      rw [h k]
  | zero => intro ρ₁ ρ₂ σ h; simp [subst]
  | succ t iht => intro ρ₁ ρ₂ σ h; simp [subst, iht ρ₁ ρ₂ σ h]
  | rect z s t ihz ihs iht => intro ρ₁ ρ₂ σ h; simp [subst, ihz ρ₁ ρ₂ σ h, ihs ρ₁ ρ₂ σ h, iht ρ₁ ρ₂ σ h]

theorem subst_lift {t v : Term} {σ : Substitution} :
  (t[⇑σ])[v] = t [v ⋆ σ] := by
  apply subst_fuse
  intro k
  exact substVar_lift

theorem WHNorm.rectNe {z s t t' : Term}
  (h : WHNorm t t') : WHNorm (rect z s t) (rect z s t') := by
  induction h; apply WHNorm.refl
  case _ t₁ t₂ t₃ _ _ _ =>
    apply WHNorm.step (t' := rect z s t₂) <;> grind [WHRed]

theorem comp_app
  (h₁ : Comp (A ⟶ B) t) (h₂ : Comp A u) : Comp B (t.app u) := by
  simp [Comp] at h₁
  have ⟨v_fun, ⟨h₁a, h₁b⟩⟩ := h₁
  cases h₁b
  case vallam t' comp_t' =>
  apply comp_exp (v := (t'.lam).app u)
  . apply comp_exp (v := t'[u])
    . grind
    . apply WHNorm.appLam
  . apply WHNorm.appNe
    exact h₁a

theorem rect_comp {A : Ty} {z s v : Term}
    (valv : ValNat v) (hz : Comp A z) (hs : Comp (nat ⟶ A ⟶ A) s) :
    Comp A (rect z s v) := by
  induction valv with
  | valzero =>
    apply comp_exp (v := z) hz
    apply WHNorm.step WHRed.rectz WHNorm.refl
  | valSucc valk ih =>
    rename_i k
    apply comp_exp (v := (s.app k).app (rect z s k))
    . exact comp_app (comp_app hs (comp_val_nat valk)) ih
    . apply WHNorm.step WHRed.rects WHNorm.refl

theorem comp_lookup {Γ : Ctxt} {σ : Substitution} (compEnv : CompEnv Γ σ) :
    ∀ (n : Nat) (h : n < Γ.length), Comp (Γ[n]) (substVar n σ) := by
  induction compEnv with
  | empty => intro n h; simp at h
  | cons hty hEnv ih =>
    intro n h
    cases n with
    | zero => simpa [substVar] using hty
    | succ n => simpa [substVar] using ih n (by simpa using h)

theorem comp_ty
        (typed : HasType Γ t ty)
        (compEnv : CompEnv Γ σ)
        : Comp ty (t[σ]) := by
  revert compEnv σ
  induction typed
  case _ n Γ h =>
    intro σ compEnv
    simp [subst]
    exact comp_lookup compEnv n h
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
  case _ =>
    intro σ compEnv
    rename_i Γ' z' A' s' t' hz hs ht ihz ihs iht
    simp [subst]
    have hz' := ihz compEnv
    have hs' := ihs compEnv
    have ht' := iht compEnv
    simp [Comp] at ht'
    have ⟨v, hv, valv⟩ := ht'
    apply comp_exp (v := rect (z'[σ]) (s'[σ]) v)
    . exact rect_comp valv hz' hs'
    . apply WHNorm.rectNe
      exact hv

