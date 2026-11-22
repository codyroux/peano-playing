import Init.Grind.Tactics


inductive Term where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term
| zero : Term
| succ : Term → Term
| rect : Term → Term → Term → Term
| pair : Term → Term → Term
| fst : Term → Term
| snd : Term → Term

inductive Ty where
| nat : Ty
| arrow : Ty → Ty → Ty
| prod : Ty → Ty → Ty

infixr:30 " ⟶ " => Ty.arrow
infixr:35 " ⊗ " => Ty.prod

abbrev Ctxt := List Ty

open Term Ty

/-- Application, `t ⬝ u := app t u`. -/
infixl:100 " ⬝ " => Term.app

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
| pair : HasType Γ a A → HasType Γ b B → HasType Γ (pair a b) (A ⊗ B)
| fst : HasType Γ t (A ⊗ B) → HasType Γ (fst t) A
| snd : HasType Γ t (A ⊗ B) → HasType Γ (snd t) B

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
| pair a b => pair (substRen a τ) (substRen b τ)
| fst t => fst (substRen t τ)
| snd t => snd (substRen t τ)

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
| pair a b => pair (subst a σ) (subst b σ)
| fst t' => fst (subst t' σ)
| snd t' => snd (subst t' σ)

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
| fstNe : WHRed t t' → WHRed (fst t) (fst t')
| sndNe : WHRed t t' → WHRed (snd t) (snd t')
| fstPair : WHRed (fst (pair a b)) a
| sndPair : WHRed (snd (pair a b)) b

-- This is somehwere in the stdlib whatever
inductive WHNorm : Term → Term → Prop where
| refl : WHNorm t t
| step : WHRed t t' → WHNorm t' t'' → WHNorm t t''

infix:50 " ⇒* " => WHNorm

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

inductive ValProd (Comp₁ Comp₂ : Term → Prop) : Term → Prop
| valpair : Comp₁ a → Comp₂ b → ValProd Comp₁ Comp₂ (pair a b)

def Comp (ty : Ty) (t : Term) : Prop :=
match ty with
| nat => ∃ v, WHNorm t v ∧ ValNat v
| ty₁ ⟶ ty₂ => ∃ v, WHNorm t v ∧ ValArrow (Comp ty₁) (Comp ty₂) v
| ty₁ ⊗ ty₂ => ∃ v, WHNorm t v ∧ ValProd (Comp ty₁) (Comp ty₂) v

infix:30 " ⊩ᶜ " => (fun t ty => Comp ty t)

#check zero ⊩ᶜ nat

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
  all_goals
    have ⟨v', _⟩ := h₁
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
  | pair t u iht ihu => intro τ₁ τ₂ h; simp [substRen, iht τ₁ τ₂ h, ihu τ₁ τ₂ h]
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
  | fst t iht => intro τ₁ τ₂ h; simp [substRen, iht τ₁ τ₂ h]
  | snd t iht => intro τ₁ τ₂ h; simp [substRen, iht τ₁ τ₂ h]
  | rect z s t ihz ihs iht => intro τ₁ τ₂ h; simp [substRen, ihz τ₁ τ₂ h, ihs τ₁ τ₂ h, iht τ₁ τ₂ h]

theorem subst_congr (t : Term) :
    ∀ σ₁ σ₂ : Substitution, (∀ k, substVar k σ₁ = substVar k σ₂) → subst t σ₁ = subst t σ₂ := by
  induction t with
  | var k => intro σ₁ σ₂ h; simp [subst, h k]
  | app t u iht ihu => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h, ihu σ₁ σ₂ h]
  | pair t u iht ihu => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h, ihu σ₁ σ₂ h]
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
  | fst t iht => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h]
  | snd t iht => intro σ₁ σ₂ h; simp [subst, iht σ₁ σ₂ h]
  | rect z s t ihz ihs iht => intro σ₁ σ₂ h; simp [subst, ihz σ₁ σ₂ h, ihs σ₁ σ₂ h, iht σ₁ σ₂ h]

theorem substRen_comp (t : Term) :
    ∀ τ₁ τ₂ : Renaming, substRen (substRen t τ₁) τ₂ = substRen t (τ₁.comp τ₂) := by
  induction t with
  | var k => intro τ₁ τ₂; simp [substRen, renVar]
  | app t u iht ihu => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂, ihu τ₁ τ₂]
  | pair t u iht ihu => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂, ihu τ₁ τ₂]
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
  | fst t iht => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂]
  | snd t iht => intro τ₁ τ₂; simp [substRen, iht τ₁ τ₂]
  | rect z s t ihz ihs iht => intro τ₁ τ₂; simp [substRen, ihz τ₁ τ₂, ihs τ₁ τ₂, iht τ₁ τ₂]

theorem subst_ren_fuse (t : Term) :
    ∀ (ρ : Substitution) (τ : Renaming), subst t (ρ.comp τ) = substRen (subst t ρ) τ := by
  induction t with
  | var k => intro ρ τ; simp [subst, substVar]
  | app t u iht ihu => intro ρ τ; simp [subst, substRen, iht ρ τ, ihu ρ τ]
  | pair t u iht ihu => intro ρ τ; simp [subst, substRen, iht ρ τ, ihu ρ τ]
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
  | fst t iht => intro ρ τ; simp [subst, substRen, iht ρ τ]
  | snd t iht => intro ρ τ; simp [subst, substRen, iht ρ τ]
  | rect z s t ihz ihs iht => intro ρ τ; simp [subst, substRen, ihz ρ τ, ihs ρ τ, iht ρ τ]

theorem ren_subst_fuse (t : Term) :
    ∀ (τ : Renaming) (ρ σ : Substitution),
      (∀ k, substVar (renVar k τ) ρ = substVar k σ) →
      subst (substRen t τ) ρ = subst t σ := by
  induction t with
  | var k => intro τ ρ σ h; simp [substRen, subst, h k]
  | app t u iht ihu => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h, ihu τ ρ σ h]
  | pair t u iht ihu => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h, ihu τ ρ σ h]
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
  | fst t iht => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h]
  | snd t iht => intro τ ρ σ h; simp [substRen, subst, iht τ ρ σ h]
  | rect z s t ihz ihs iht => intro τ ρ σ h; simp [substRen, subst, ihz τ ρ σ h, ihs τ ρ σ h, iht τ ρ σ h]

theorem subst_id (t : Term) : t [id] = t := by
  induction t with
  | var k => simp [subst, substVar, renVar]
  | app t u iht ihu => simp [subst, iht, ihu]
  | pair t u iht ihu => simp [subst, iht, ihu]
  | lam t iht =>
    simp only [subst]
    congr 1
    rw [subst_congr t (⇑ id) id (by intro k; cases k <;> simp [lift, substVar, substRen, renVar])]
    exact iht
  | zero => simp [subst]
  | succ t iht => simp [subst, iht]
  | fst t iht => simp [subst, iht]
  | snd t iht => simp [subst, iht]
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
  | pair t u iht ihu => intro ρ₁ ρ₂ σ h; simp [subst, iht ρ₁ ρ₂ σ h, ihu ρ₁ ρ₂ σ h]
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
  | fst t iht => intro ρ₁ ρ₂ σ h; simp [subst, iht ρ₁ ρ₂ σ h]
  | snd t iht => intro ρ₁ ρ₂ σ h; simp [subst, iht ρ₁ ρ₂ σ h]
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

theorem WHNorm.fstNe {t t' : Term} (h : WHNorm t t') : WHNorm (fst t) (fst t') := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (.fstNe r) ih

theorem WHNorm.sndNe {t t' : Term} (h : WHNorm t t') : WHNorm (snd t) (snd t') := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (.sndNe r) ih

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
  case pair =>
    rename_i iha ihb
    intro σ compEnv
    simp only [subst, Comp]
    exact ⟨_, WHNorm.refl, ValProd.valpair (iha compEnv) (ihb compEnv)⟩
  case fst =>
    rename_i iht
    intro σ compEnv
    have h := iht compEnv
    simp only [Comp] at h
    obtain ⟨v, hv, hval⟩ := h
    cases hval with
    | valpair ha _ =>
      simp only [subst]
      exact comp_exp ha ((WHNorm.fstNe hv).trans (WHNorm.step WHRed.fstPair WHNorm.refl))
  case snd =>
    rename_i iht
    intro σ compEnv
    have h := iht compEnv
    simp only [Comp] at h
    obtain ⟨v, hv, hval⟩ := h
    cases hval with
    | valpair _ hb =>
      simp only [subst]
      exact comp_exp hb ((WHNorm.sndNe hv).trans (WHNorm.step WHRed.sndPair WHNorm.refl))


-- I guess we could have used this before, maybe we'll go back
-- and change it.
def Val (ty : Ty) (v : Term) : Prop :=
match ty with
| nat => ValNat v
| ty₁ ⟶ ty₂ => ValArrow (Val ty₁) (Val ty₂) v
| ty₁ ⊗ ty₂ => ValProd (Val ty₁) (Val ty₂) v

def Eval (t : Term) (ty : Ty) (v : Term) : Prop :=
  HasType [] t ty ∧ WHNorm t v ∧ Val ty v

/-! ## Encoding terms as natural numbers

We go in two steps: first a Gödel numbering `code : Term → Nat` built from
the Cantor pairing function, then the numeral of that number as a closed
term of type `nat`. -/

/-- Triangular numbers, defined recursively to avoid division:
`tri n = n * (n + 1) / 2`. -/
def tri : Nat → Nat
| 0 => 0
| n + 1 => tri n + n + 1

theorem tri_lt {s s' : Nat} (h : s < s') : tri s + s + 1 ≤ tri s' := by
  induction s' with
  | zero => omega
  | succ s' ih =>
    simp only [tri]
    by_cases hs : s = s'
    · subst hs; omega
    · have := ih (by omega); omega

/-- The Cantor pairing function. -/
def npair (a b : Nat) : Nat := tri (a + b) + b

theorem npair_inj {a b c d : Nat} (h : npair a b = npair c d) : a = c ∧ b = d := by
  unfold npair at h
  rcases Nat.lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
  · have := tri_lt hlt; omega
  · rw [heq] at h; omega
  · have := tri_lt hgt; omega

@[simp]
theorem npair_eq_iff {a b c d : Nat} : npair a b = npair c d ↔ a = c ∧ b = d :=
  ⟨npair_inj, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

/-- Gödel numbering of terms: a tag for the head constructor, paired with
the (paired) codes of the arguments. -/
def code : Term → Nat
| var n => npair 0 n
| app t u => npair 1 (npair (code t) (code u))
| lam t => npair 2 (code t)
| zero => npair 3 0
| succ t => npair 4 (code t)
| rect z s t => npair 5 (npair (code z) (npair (code s) (code t)))
| pair a b => npair 6 (npair (code a) (code b))
| fst t => npair 7 (code t)
| snd t => npair 8 (code t)

theorem code_inj {t t' : Term} (h : code t = code t') : t = t' := by
  induction t generalizing t' with
  | var n => cases t' <;> simp_all [code]
  | app t u iht ihu =>
    cases t' <;> simp [code] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [iht h₁, ihu h₂]
  | lam t ih =>
    cases t' <;> simp [code] at h
    rw [ih h]
  | zero => cases t' <;> simp_all [code]
  | succ t ih =>
    cases t' <;> simp [code] at h
    rw [ih h]
  | rect z s t ihz ihs iht =>
    cases t' <;> simp [code] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    rw [ihz h₁, ihs h₂, iht h₃]
  | pair a b iha ihb =>
    cases t' <;> simp [code] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [iha h₁, ihb h₂]
  | fst t ih =>
    cases t' <;> simp [code] at h
    rw [ih h]
  | snd t ih =>
    cases t' <;> simp [code] at h
    rw [ih h]

/-- The numeral `succ^n zero`. -/
def numeral : Nat → Term
| 0 => zero
| n + 1 => succ (numeral n)

/-- Numeric literals denote numerals: `(3 : Term) = succ (succ (succ zero))`. -/
instance {n : Nat} : OfNat Term n := ⟨numeral n⟩

@[simp] theorem ofNat_eq_numeral {n : Nat} : (OfNat.ofNat n : Term) = numeral n := rfl

theorem numeral_typed {Γ : Ctxt} (n : Nat) : HasType Γ (numeral n) nat := by
  induction n with
  | zero => exact HasType.zero
  | succ n ih => exact HasType.succ ih

theorem numeral_val (n : Nat) : ValNat (numeral n) := by
  induction n with
  | zero => exact ValNat.valzero
  | succ n ih => exact ValNat.valSucc ih

theorem numeral_inj {n m : Nat} (h : numeral n = numeral m) : n = m := by
  induction n generalizing m with
  | zero => cases m <;> simp_all [numeral]
  | succ n ih =>
    cases m with
    | zero => simp [numeral] at h
    | succ m => simp only [numeral, Term.succ.injEq] at h; rw [ih h]

/-- The Cantor quotation of a term: the numeral of its Gödel number. -/
def quote (t : Term) : Term := numeral (code t)

/-! ## Encodings and quotation notation -/

/-- An encoding of terms as closed natural number values. Quotation
`⌜t⌝` refers to the `Encoding` instance in scope. -/
class Encoding where
  encode : Term → Term
  is_nat_encode : ∀ t, HasType [] (encode t) nat
  is_val_encode : ∀ t, ValNat (encode t)
  encode_inj : ∀ t t', encode t = encode t' → t = t'

notation "⌜" t "⌝" => Encoding.encode t

instance (priority := low) cantorEncoding : Encoding where
  encode := quote
  is_nat_encode t := numeral_typed (code t)
  is_val_encode t := numeral_val (code t)
  encode_inj _ _ h := code_inj (numeral_inj h)

theorem cantor_quote (t : Term) : ⌜t⌝ = numeral (code t) := rfl

/-! The encoding is compositional: the code of a term is computed from the
codes of its immediate subterms (by definition). -/

theorem code_app (t u : Term) : code (t ⬝ u) = npair 1 (npair (code t) (code u)) := rfl
theorem code_lam (t : Term) : code (lam t) = npair 2 (code t) := rfl
theorem code_succ (t : Term) : code (succ t) = npair 4 (code t) := rfl
theorem code_rect (z s t : Term) :
    code (rect z s t) = npair 5 (npair (code z) (npair (code s) (code t))) := rfl

#eval code (lam (var 0))
#eval code (lam (var 0) ⬝ 0)

/-! ## The encoding inside System T

We implement `npair`, and from it the term constructors on codes, as closed
T-terms, and show they compute correctly. Because reduction is call-by-name,
the specifications only ask that arguments *reduce* to numerals. -/

theorem WHNorm.beta2 {t a b : Term} :
    lam (lam t) ⬝ a ⬝ b ⇒* subst t (b ⋆ a ⋆ id) := by
  apply WHNorm.step (WHRed.appNe WHRed.appLam)
  show lam (subst t (lift (a ⋆ id))) ⬝ b ⇒* _
  rw [← subst_lift]
  exact WHNorm.appLam

@[simp]
theorem numeral_subst {n : Nat} {σ : Substitution} : subst (numeral n) σ = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, subst, ih]

/-- Iteration on numerals: if `z` computes `f 0` and `s` maps `k`, `f k` to
`f (k+1)`, then `rect z s` computes `f`. -/
theorem rect_iter {z s : Term} (f : Nat → Nat)
    (hz : z ⇒* numeral (f 0))
    (hs : ∀ k t, t ⇒* numeral (f k) → s ⬝ numeral k ⬝ t ⇒* numeral (f (k + 1))) :
    ∀ n, rect z s (numeral n) ⇒* numeral (f n)
  | 0 => WHNorm.step WHRed.rectz hz
  | n + 1 => WHNorm.step WHRed.rects (hs n _ (rect_iter f hz hs n))

theorem rect_spec {z s a : Term} {n : Nat} (f : Nat → Nat)
    (hz : z ⇒* numeral (f 0))
    (hs : ∀ k t, t ⇒* numeral (f k) → s ⬝ numeral k ⬝ t ⇒* numeral (f (k + 1)))
    (ha : a ⇒* numeral n) :
    rect z s a ⇒* numeral (f n) :=
  (WHNorm.rectNe ha).trans (rect_iter f hz hs n)

/-! ### Addition -/

/-- `fun _ acc => succ acc` -/
def addStep : Term := lam (lam (succ (var 0)))

/-- `fun x y => rect y addStep x` -/
def addT : Term := lam (lam (rect (var 0) addStep (var 1)))

@[simp] theorem addStep_subst {σ : Substitution} : subst addStep σ = addStep := by
  simp [addStep, subst, substVar, lift]

@[simp] theorem addT_subst {σ : Substitution} : subst addT σ = addT := by
  simp [addT, subst, substVar, lift, substRen, renVar]

theorem addT_spec {a b : Term} {n m : Nat}
    (ha : a ⇒* numeral n) (hb : b ⇒* numeral m) :
    addT ⬝ a ⬝ b ⇒* numeral (n + m) := by
  unfold addT
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, addStep_subst, Nat.one_ne_zero, ite_false, ite_true,
    Nat.add_one_sub_one]
  rw [Nat.add_comm]
  apply rect_spec (fun k => m + k) hb _ ha
  intro k t ht
  unfold addStep
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, ite_true]
  exact WHNorm.succ ht

/-! ### Triangular numbers -/

/-- `fun k acc => succ (k + acc)` -/
def triStep : Term := lam (lam (succ (addT ⬝ var 1 ⬝ var 0)))

/-- `fun x => rect 0 triStep x` -/
def triT : Term := lam (rect 0 triStep (var 0))

@[simp] theorem triStep_subst {σ : Substitution} : subst triStep σ = triStep := by
  simp [triStep, subst, substVar, lift, substRen, renVar]

@[simp] theorem triT_subst {σ : Substitution} : subst triT σ = triT := by
  simp [triT, subst, substVar, lift]

theorem triT_spec {a : Term} {n : Nat} (ha : a ⇒* numeral n) :
    triT ⬝ a ⇒* numeral (tri n) := by
  unfold triT
  apply WHNorm.trans WHNorm.appLam
  simp only [subst, substVar, triStep_subst, ofNat_eq_numeral, numeral_subst, ite_true]
  apply rect_spec tri WHNorm.refl _ ha
  intro k t ht
  unfold triStep
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, addT_subst, Nat.one_ne_zero, ite_false, ite_true,
    Nat.add_one_sub_one]
  have : tri (k + 1) = (k + tri k) + 1 := by simp only [tri]; omega
  rw [this]
  exact WHNorm.succ (addT_spec WHNorm.refl ht)

/-! ### Pairing -/

/-- `fun a b => tri (a + b) + b` -/
def pairT : Term := lam (lam (addT ⬝ (triT ⬝ (addT ⬝ var 1 ⬝ var 0)) ⬝ var 0))

@[simp] theorem pairT_subst {σ : Substitution} : subst pairT σ = pairT := by
  simp [pairT, subst, substVar, lift, substRen, renVar]

theorem pairT_spec {a b : Term} {n m : Nat}
    (ha : a ⇒* numeral n) (hb : b ⇒* numeral m) :
    pairT ⬝ a ⬝ b ⇒* numeral (npair n m) := by
  unfold pairT
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, addT_subst, triT_subst, Nat.one_ne_zero, ite_false,
    ite_true, Nat.add_one_sub_one]
  exact addT_spec (triT_spec (addT_spec ha hb)) hb

/-! ### Constructors on codes -/

/-- `AppT ⬝ ⌜t⌝ ⬝ ⌜u⌝ ⇒* ⌜t ⬝ u⌝` -/
def AppT : Term := lam (lam (pairT ⬝ 1 ⬝ (pairT ⬝ var 1 ⬝ var 0)))

@[simp] theorem AppT_subst {σ : Substitution} : subst AppT σ = AppT := by
  simp [AppT, subst, substVar, lift, substRen, renVar]

theorem AppT_spec {a b t u : Term} (ha : a ⇒* ⌜t⌝) (hb : b ⇒* ⌜u⌝) :
    AppT ⬝ a ⬝ b ⇒* ⌜t ⬝ u⌝ := by
  unfold AppT
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, pairT_subst, ofNat_eq_numeral, numeral_subst,
    Nat.one_ne_zero, ite_false, ite_true, Nat.add_one_sub_one]
  exact pairT_spec WHNorm.refl (pairT_spec ha hb)

/-- `fun _ acc => npair 4 acc`, i.e. `⌜n⌝ ↦ ⌜succ n⌝` -/
def quoteStep : Term := lam (lam (pairT ⬝ 4 ⬝ var 0))

/-- `QuoteT ⬝ n ⇒* ⌜n⌝` for numerals `n`, hence `QuoteT ⬝ ⌜t⌝ ⇒* ⌜⌜t⌝⌝`. -/
def QuoteT : Term := lam (rect (pairT ⬝ 3 ⬝ 0) quoteStep (var 0))

@[simp] theorem quoteStep_subst {σ : Substitution} : subst quoteStep σ = quoteStep := by
  simp [quoteStep, subst, substVar, lift]

@[simp] theorem QuoteT_subst {σ : Substitution} : subst QuoteT σ = QuoteT := by
  simp [QuoteT, subst, substVar, lift]

theorem QuoteT_spec_numeral {a : Term} {n : Nat} (ha : a ⇒* numeral n) :
    QuoteT ⬝ a ⇒* ⌜numeral n⌝ := by
  unfold QuoteT
  apply WHNorm.trans WHNorm.appLam
  simp only [subst, substVar, pairT_subst, ofNat_eq_numeral, numeral_subst,
    quoteStep_subst, ite_true]
  apply rect_spec (fun k => code (numeral k)) (pairT_spec (n := 3) WHNorm.refl WHNorm.refl) _ ha
  intro k t ht
  unfold quoteStep
  apply WHNorm.trans WHNorm.beta2
  simp only [subst, substVar, pairT_subst, ofNat_eq_numeral, numeral_subst, ite_true]
  exact pairT_spec (n := 4) WHNorm.refl ht

theorem QuoteT_spec {a t : Term} (ha : a ⇒* ⌜t⌝) : QuoteT ⬝ a ⇒* ⌜⌜t⌝⌝ :=
  QuoteT_spec_numeral ha

/-! ### Typing -/

theorem addStep_typed {Γ : Ctxt} : HasType Γ addStep (nat ⟶ nat ⟶ nat) :=
  .lam (.lam (.succ (.var (n := 0) (by simp))))

theorem addT_typed {Γ : Ctxt} : HasType Γ addT (nat ⟶ nat ⟶ nat) :=
  .lam (.lam (.rect (.var (n := 0) (by simp)) addStep_typed (.var (n := 1) (by simp))))

theorem triT_typed {Γ : Ctxt} : HasType Γ triT (nat ⟶ nat) :=
  .lam (.rect (numeral_typed 0)
    (.lam (.lam (.succ (.app (.app addT_typed (.var (n := 1) (by simp)))
      (.var (n := 0) (by simp))))))
    (.var (n := 0) (by simp)))

theorem pairT_typed {Γ : Ctxt} : HasType Γ pairT (nat ⟶ nat ⟶ nat) :=
  .lam (.lam (.app (.app addT_typed
    (.app triT_typed (.app (.app addT_typed (.var (n := 1) (by simp)))
      (.var (n := 0) (by simp)))))
    (.var (n := 0) (by simp))))

theorem AppT_typed {Γ : Ctxt} : HasType Γ AppT (nat ⟶ nat ⟶ nat) :=
  .lam (.lam (.app (.app pairT_typed (numeral_typed 1))
    (.app (.app pairT_typed (.var (n := 1) (by simp))) (.var (n := 0) (by simp)))))

theorem QuoteT_typed {Γ : Ctxt} : HasType Γ QuoteT (nat ⟶ nat) :=
  .lam (.rect (.app (.app pairT_typed (numeral_typed 3)) (numeral_typed 0))
    (.lam (.lam (.app (.app pairT_typed (numeral_typed 4)) (.var (n := 0) (by simp)))))
    (.var (n := 0) (by simp)))

/-! ## Reasonable encodings

An encoding is *reasonable* when application and quotation of codes are
T-definable; this is exactly what self-application `t ⬝ ⌜t⌝` needs. -/

class ReasonableEncoding extends Encoding where
  appT : Term
  quoteT : Term
  appT_typed : ∀ {Γ}, HasType Γ appT (nat ⟶ nat ⟶ nat)
  quoteT_typed : ∀ {Γ}, HasType Γ quoteT (nat ⟶ nat)
  appT_spec : ∀ {a b t u}, a ⇒* encode t → b ⇒* encode u → appT ⬝ a ⬝ b ⇒* encode (t ⬝ u)
  quoteT_spec : ∀ {a t}, a ⇒* encode t → quoteT ⬝ a ⇒* encode (encode t)

instance cantorReasonable : ReasonableEncoding where
  toEncoding := cantorEncoding
  appT := AppT
  quoteT := QuoteT
  appT_typed := AppT_typed
  quoteT_typed := QuoteT_typed
  appT_spec := AppT_spec
  quoteT_spec := QuoteT_spec

/-! ## Uniqueness of normal forms

Weak-head reduction is not confluent on its own: `rect z s (succ u)` can
either fire `rects` or reduce `u`, and the results only join under full
reduction. We go through Tait–Martin-Löf parallel reduction, whose reflexive
transitive closure contains `⇒*` and is confluent (Takahashi's complete
development). Numerals are normal for it, hence unique. -/

inductive Par : Term → Term → Prop where
| pvar : Par (var k) (var k)
| papp : Par t t' → Par u u' → Par (app t u) (app t' u')
| plam : Par t t' → Par (lam t) (lam t')
| pzero : Par zero zero
| psucc : Par t t' → Par (succ t) (succ t')
| prect : Par z z' → Par s s' → Par t t' → Par (rect z s t) (rect z' s' t')
| pbeta : Par t t' → Par u u' → Par (app (lam t) u) (subst t' (u' ⋆ id))
| prectz : Par z z' → Par (rect z s zero) z'
| prects : Par z z' → Par s s' → Par t t' →
    Par (rect z s (succ t)) (app (app s' t') (rect z' s' t'))
| ppair : Par a a' → Par b b' → Par (pair a b) (pair a' b')
| pfst : Par t t' → Par (fst t) (fst t')
| psnd : Par t t' → Par (snd t) (snd t')
| pfstβ : Par a a' → Par (fst (pair a b)) a'
| psndβ : Par b b' → Par (snd (pair a b)) b'

theorem par_refl : ∀ t, Par t t
  | var _ => .pvar
  | app t u => .papp (par_refl t) (par_refl u)
  | lam t => .plam (par_refl t)
  | zero => .pzero
  | succ t => .psucc (par_refl t)
  | rect z s t => .prect (par_refl z) (par_refl s) (par_refl t)
  | pair a b => .ppair (par_refl a) (par_refl b)
  | fst t => .pfst (par_refl t)
  | snd t => .psnd (par_refl t)

theorem ren_beta {t u : Term} {τ : Renaming} :
    substRen (subst t (u ⋆ id)) τ = subst (substRen t (liftRen τ)) (substRen u τ ⋆ id) := by
  rw [← subst_ren_fuse]
  symm
  apply ren_subst_fuse
  intro k
  cases k <;> simp [renVar, liftRen, substVar, substRen]

theorem subst_beta {t u : Term} {σ : Substitution} :
    subst (subst t (u ⋆ id)) σ = subst (subst t (lift σ)) (subst u σ ⋆ id) := by
  rw [subst_lift]
  apply subst_fuse
  intro k
  cases k <;> simp [substVar, subst, renVar]

theorem par_ren {t t' : Term} (h : Par t t') : ∀ τ, Par (substRen t τ) (substRen t' τ) := by
  induction h with
  | pvar => intro τ; exact .pvar
  | papp _ _ ih₁ ih₂ => intro τ; exact .papp (ih₁ τ) (ih₂ τ)
  | plam _ ih => intro τ; exact .plam (ih _)
  | pzero => intro τ; exact .pzero
  | psucc _ ih => intro τ; exact .psucc (ih τ)
  | prect _ _ _ ihz ihs iht => intro τ; exact .prect (ihz τ) (ihs τ) (iht τ)
  | pbeta _ _ iht ihu => intro τ; rw [ren_beta]; exact .pbeta (iht _) (ihu τ)
  | prectz _ ihz => intro τ; exact .prectz (ihz τ)
  | prects _ _ _ ihz ihs iht => intro τ; exact .prects (ihz τ) (ihs τ) (iht τ)
  | ppair _ _ iha ihb => intro τ; exact .ppair (iha τ) (ihb τ)
  | pfst _ ih => intro τ; exact .pfst (ih τ)
  | psnd _ ih => intro τ; exact .psnd (ih τ)
  | pfstβ _ ih => intro τ; exact .pfstβ (ih τ)
  | psndβ _ ih => intro τ; exact .psndβ (ih τ)

theorem par_lift {σ σ' : Substitution} (hσ : ∀ k, Par (substVar k σ) (substVar k σ')) :
    ∀ k, Par (substVar k (lift σ)) (substVar k (lift σ')) := by
  intro k
  cases k with
  | zero => simp only [lift, substVar, ite_true]; exact .pvar
  | succ k =>
    simp only [lift, substVar, Nat.add_one_ne_zero, ite_false, Nat.add_one_sub_one]
    exact par_ren (hσ k) _

theorem par_subst {t t' : Term} (h : Par t t') :
    ∀ σ σ', (∀ k, Par (substVar k σ) (substVar k σ')) → Par (subst t σ) (subst t' σ') := by
  induction h with
  | @pvar k => intro σ σ' hσ; exact hσ k
  | papp _ _ ih₁ ih₂ => intro σ σ' hσ; exact .papp (ih₁ σ σ' hσ) (ih₂ σ σ' hσ)
  | plam _ ih => intro σ σ' hσ; exact .plam (ih _ _ (par_lift hσ))
  | pzero => intro σ σ' hσ; exact .pzero
  | psucc _ ih => intro σ σ' hσ; exact .psucc (ih σ σ' hσ)
  | prect _ _ _ ihz ihs iht =>
    intro σ σ' hσ; exact .prect (ihz σ σ' hσ) (ihs σ σ' hσ) (iht σ σ' hσ)
  | pbeta _ _ iht ihu =>
    intro σ σ' hσ; rw [subst_beta]; exact .pbeta (iht _ _ (par_lift hσ)) (ihu σ σ' hσ)
  | prectz _ ihz => intro σ σ' hσ; exact .prectz (ihz σ σ' hσ)
  | prects _ _ _ ihz ihs iht =>
    intro σ σ' hσ; exact .prects (ihz σ σ' hσ) (ihs σ σ' hσ) (iht σ σ' hσ)
  | ppair _ _ iha ihb => intro σ σ' hσ; exact .ppair (iha σ σ' hσ) (ihb σ σ' hσ)
  | pfst _ ih => intro σ σ' hσ; exact .pfst (ih σ σ' hσ)
  | psnd _ ih => intro σ σ' hσ; exact .psnd (ih σ σ' hσ)
  | pfstβ _ ih => intro σ σ' hσ; exact .pfstβ (ih σ σ' hσ)
  | psndβ _ ih => intro σ σ' hσ; exact .psndβ (ih σ σ' hσ)

/-- The complete development: contract every redex visible in the term. -/
def cd : Term → Term
| var k => var k
| app (lam t) u => subst (cd t) (cd u ⋆ id)
| app t u => app (cd t) (cd u)
| lam t => lam (cd t)
| zero => zero
| succ t => succ (cd t)
| rect z _ zero => cd z
| rect z s (succ t) => app (app (cd s) (cd t)) (rect (cd z) (cd s) (cd t))
| rect z s t => rect (cd z) (cd s) (cd t)
| pair a b => pair (cd a) (cd b)
| fst (pair a _) => cd a
| fst t => fst (cd t)
| snd (pair _ b) => cd b
| snd t => snd (cd t)

theorem par_lam_inv {t t' : Term} (h : Par (lam t) (lam t')) : Par t t' := by
  cases h; assumption

theorem par_succ_inv {t t' : Term} (h : Par (succ t) (succ t')) : Par t t' := by
  cases h; assumption

theorem par_pair_inv {a b a' b' : Term} (h : Par (pair a b) (pair a' b')) :
    Par a a' ∧ Par b b' := by
  cases h; exact ⟨by assumption, by assumption⟩

/-- Takahashi's triangle: every parallel step can be completed to `cd`. -/
theorem par_triangle {t t' : Term} (h : Par t t') : Par t' (cd t) := by
  induction h with
  | pvar => exact .pvar
  | @papp t t₁ u u₁ ht _ iht ihu =>
    cases t with
    | lam b =>
      cases ht
      exact .pbeta (par_lam_inv iht) ihu
    | _ => exact .papp iht ihu
  | plam _ ih => exact .plam ih
  | pzero => exact .pzero
  | psucc _ ih => exact .psucc ih
  | @prect z z₁ s s₁ t t₁ _ _ ht ihz ihs iht =>
    cases t with
    | zero => cases ht; exact .prectz ihz
    | succ v => cases ht; exact .prects ihz ihs (par_succ_inv iht)
    | _ => exact .prect ihz ihs iht
  | @pbeta t t₁ u u₁ _ _ iht ihu =>
    refine par_subst iht (u₁ ⋆ id) (cd u ⋆ id) ?_
    intro k
    cases k with
    | zero => exact ihu
    | succ k => exact par_refl _
  | prectz _ ihz => exact ihz
  | prects _ _ _ ihz ihs iht => exact .papp (.papp ihs iht) (.prect ihz ihs iht)
  | ppair _ _ iha ihb => exact .ppair iha ihb
  | @pfst t t₁ ht ih =>
    cases t with
    | pair a b => cases ht; exact .pfstβ (par_pair_inv ih).1
    | _ => exact .pfst ih
  | @psnd t t₁ ht ih =>
    cases t with
    | pair a b => cases ht; exact .psndβ (par_pair_inv ih).2
    | _ => exact .psnd ih
  | pfstβ _ ih => exact ih
  | psndβ _ ih => exact ih

inductive ParStar : Term → Term → Prop where
| refl : ParStar t t
| step : Par t t' → ParStar t' t'' → ParStar t t''

theorem par_strip {t a b : Term} (h₁ : Par t a) (h₂ : ParStar t b) :
    ∃ w, ParStar a w ∧ Par b w := by
  induction h₂ generalizing a with
  | refl => exact ⟨a, .refl, h₁⟩
  | step p _ ih =>
    obtain ⟨w, hw, hbw⟩ := ih (par_triangle p)
    exact ⟨w, .step (par_triangle h₁) hw, hbw⟩

theorem parStar_confluent {t a b : Term} (h₁ : ParStar t a) (h₂ : ParStar t b) :
    ∃ w, ParStar a w ∧ ParStar b w := by
  induction h₁ generalizing b with
  | refl => exact ⟨b, h₂, .refl⟩
  | step p _ ih =>
    obtain ⟨w₁, hw₁, hbw₁⟩ := par_strip p h₂
    obtain ⟨w, haw, hw₁w⟩ := ih hw₁
    exact ⟨w, haw, .step hbw₁ hw₁w⟩

theorem whred_par {t t' : Term} (h : WHRed t t') : Par t t' := by
  induction h with
  | appNe _ ih => exact .papp ih (par_refl _)
  | appLam => exact .pbeta (par_refl _) (par_refl _)
  | rectNe _ ih => exact .prect (par_refl _) (par_refl _) ih
  | succ _ ih => exact .psucc ih
  | rectz => exact .prectz (par_refl _)
  | rects => exact .prects (par_refl _) (par_refl _) (par_refl _)
  | fstNe _ ih => exact .pfst ih
  | sndNe _ ih => exact .psnd ih
  | fstPair => exact .pfstβ (par_refl _)
  | sndPair => exact .psndβ (par_refl _)

theorem whnorm_parStar {t v : Term} (h : t ⇒* v) : ParStar t v := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (whred_par r) ih

theorem par_numeral : ∀ {n : Nat} {x : Term}, Par (numeral n) x → x = numeral n
  | 0, _, h => by change Par zero _ at h; cases h; rfl
  | n + 1, _, h => by
    change Par (succ (numeral n)) _ at h
    cases h with
    | psucc h' => rw [par_numeral h']; rfl

theorem parStar_numeral {t x : Term} {n : Nat} (h : ParStar t x) (ht : t = numeral n) :
    x = numeral n := by
  induction h with
  | refl => exact ht
  | step p _ ih => subst ht; exact ih (par_numeral p)

/-- A term reduces to at most one numeral. -/
theorem numeral_unique {t : Term} {n m : Nat} (h₁ : t ⇒* numeral n) (h₂ : t ⇒* numeral m) :
    n = m := by
  obtain ⟨w, hw₁, hw₂⟩ := parStar_confluent (whnorm_parStar h₁) (whnorm_parStar h₂)
  exact numeral_inj ((parStar_numeral hw₁ rfl).symm.trans (parStar_numeral hw₂ rfl))

/-- The diamond property of parallel reduction. -/
theorem par_diamond {t a b : Term} (h₁ : Par t a) (h₂ : Par t b) :
    ∃ w, Par a w ∧ Par b w :=
  ⟨cd t, par_triangle h₁, par_triangle h₂⟩

/-! ## Confluence of full reduction -/

/-- Full one-step reduction: β and the two `rect` rules, in any context. -/
inductive Red : Term → Term → Prop where
| beta : Red (app (lam t) u) (subst t (u ⋆ id))
| rectz : Red (rect z s zero) z
| rects : Red (rect z s (succ t)) (app (app s t) (rect z s t))
| appL : Red t t' → Red (app t u) (app t' u)
| appR : Red u u' → Red (app t u) (app t u')
| lam : Red t t' → Red (lam t) (lam t')
| succ : Red t t' → Red (succ t) (succ t')
| rectZ : Red z z' → Red (rect z s t) (rect z' s t)
| rectS : Red s s' → Red (rect z s t) (rect z s' t)
| rectT : Red t t' → Red (rect z s t) (rect z s t')
| fstβ : Red (fst (pair a b)) a
| sndβ : Red (snd (pair a b)) b
| pairL : Red a a' → Red (pair a b) (pair a' b)
| pairR : Red b b' → Red (pair a b) (pair a b')
| fst : Red t t' → Red (fst t) (fst t')
| snd : Red t t' → Red (snd t) (snd t')

inductive RedStar : Term → Term → Prop where
| refl : RedStar t t
| step : Red t t' → RedStar t' t'' → RedStar t t''

infix:50 " ⟶* " => RedStar

theorem RedStar.single {t t' : Term} (h : Red t t') : t ⟶* t' := .step h .refl

theorem RedStar.trans {t t' t'' : Term} (h₁ : t ⟶* t') (h₂ : t' ⟶* t'') : t ⟶* t'' := by
  induction h₁ with
  | refl => exact h₂
  | step r _ ih => exact .step r (ih h₂)

/-- Lift a reduction sequence through a context `f`. -/
theorem RedStar.map (f : Term → Term) (hf : ∀ {a b}, Red a b → Red (f a) (f b))
    {t t' : Term} (h : t ⟶* t') : f t ⟶* f t' := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (hf r) ih

theorem RedStar.app {t t' u u' : Term} (ht : t ⟶* t') (hu : u ⟶* u') :
    app t u ⟶* app t' u' :=
  (ht.map (Term.app · u) .appL).trans (hu.map (Term.app t' ·) .appR)

theorem RedStar.lam {t t' : Term} (h : t ⟶* t') : lam t ⟶* lam t' := h.map _ .lam

theorem RedStar.succ {t t' : Term} (h : t ⟶* t') : succ t ⟶* succ t' := h.map _ .succ

theorem RedStar.rect {z z' s s' t t' : Term} (hz : z ⟶* z') (hs : s ⟶* s') (ht : t ⟶* t') :
    rect z s t ⟶* rect z' s' t' :=
  ((hz.map (Term.rect · s t) .rectZ).trans (hs.map (Term.rect z' · t) .rectS)).trans
    (ht.map (Term.rect z' s' ·) .rectT)

theorem RedStar.pair {a a' b b' : Term} (ha : a ⟶* a') (hb : b ⟶* b') :
    pair a b ⟶* pair a' b' :=
  (ha.map (Term.pair · b) .pairL).trans (hb.map (Term.pair a' ·) .pairR)

theorem RedStar.fst {t t' : Term} (h : t ⟶* t') : fst t ⟶* fst t' := h.map _ .fst

theorem RedStar.snd {t t' : Term} (h : t ⟶* t') : snd t ⟶* snd t' := h.map _ .snd

theorem red_par {t t' : Term} (h : Red t t') : Par t t' := by
  induction h with
  | beta => exact .pbeta (par_refl _) (par_refl _)
  | rectz => exact .prectz (par_refl _)
  | rects => exact .prects (par_refl _) (par_refl _) (par_refl _)
  | appL _ ih => exact .papp ih (par_refl _)
  | appR _ ih => exact .papp (par_refl _) ih
  | lam _ ih => exact .plam ih
  | succ _ ih => exact .psucc ih
  | rectZ _ ih => exact .prect ih (par_refl _) (par_refl _)
  | rectS _ ih => exact .prect (par_refl _) ih (par_refl _)
  | rectT _ ih => exact .prect (par_refl _) (par_refl _) ih
  | fstβ => exact .pfstβ (par_refl _)
  | sndβ => exact .psndβ (par_refl _)
  | pairL _ ih => exact .ppair ih (par_refl _)
  | pairR _ ih => exact .ppair (par_refl _) ih
  | fst _ ih => exact .pfst ih
  | snd _ ih => exact .psnd ih

theorem par_redStar {t t' : Term} (h : Par t t') : t ⟶* t' := by
  induction h with
  | pvar => exact .refl
  | papp _ _ ih₁ ih₂ => exact ih₁.app ih₂
  | plam _ ih => exact ih.lam
  | pzero => exact .refl
  | psucc _ ih => exact ih.succ
  | prect _ _ _ ihz ihs iht => exact ihz.rect ihs iht
  | pbeta _ _ iht ihu => exact (iht.lam.app ihu).trans (.single .beta)
  | prectz _ ihz => exact (RedStar.single .rectz).trans ihz
  | prects _ _ _ ihz ihs iht => exact (ihz.rect ihs iht.succ).trans (.single .rects)
  | ppair _ _ iha ihb => exact iha.pair ihb
  | pfst _ ih => exact ih.fst
  | psnd _ ih => exact ih.snd
  | pfstβ _ ih => exact (RedStar.single .fstβ).trans ih
  | psndβ _ ih => exact (RedStar.single .sndβ).trans ih

theorem redStar_parStar {t t' : Term} (h : t ⟶* t') : ParStar t t' := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (red_par r) ih

theorem parStar_redStar {t t' : Term} (h : ParStar t t') : t ⟶* t' := by
  induction h with
  | refl => exact .refl
  | step p _ ih => exact (par_redStar p).trans ih

/-- **Church–Rosser** for full β/rect reduction. -/
theorem red_confluent {t a b : Term} (h₁ : t ⟶* a) (h₂ : t ⟶* b) :
    ∃ w, a ⟶* w ∧ b ⟶* w := by
  obtain ⟨w, hw₁, hw₂⟩ := parStar_confluent (redStar_parStar h₁) (redStar_parStar h₂)
  exact ⟨w, parStar_redStar hw₁, parStar_redStar hw₂⟩

/-- Weak-head reduction is a special case of full reduction. -/
theorem whnorm_redStar {t v : Term} (h : t ⇒* v) : t ⟶* v :=
  parStar_redStar (whnorm_parStar h)

/-! ## There is no self-evaluator -/

theorem ValNat.eq_numeral {v : Term} (h : ValNat v) : ∃ n, v = numeral n := by
  induction h with
  | valzero => exact ⟨0, rfl⟩
  | valSucc _ ih => obtain ⟨n, rfl⟩ := ih; exact ⟨n + 1, rfl⟩

/-- Closed terms of type `nat` evaluate to a numeral (from `comp_ty`). -/
theorem normalize {t : Term} (h : HasType [] t nat) : ∃ n, t ⇒* numeral n := by
  have hc := comp_ty h CompEnv.empty
  rw [subst_id] at hc
  simp only [Comp] at hc
  obtain ⟨v, hv, hval⟩ := hc
  obtain ⟨n, rfl⟩ := hval.eq_numeral
  exact ⟨n, hv⟩

/-- A self-evaluator computes, from the code of a closed natural number term,
the value of that term. -/
def SelfEvaluator [Encoding] (E : Term) : Prop :=
  HasType [] E (nat ⟶ nat) ∧
  ∀ t n, HasType [] t nat → t ⇒* numeral n → E ⬝ ⌜t⌝ ⇒* numeral n

theorem WHNorm.beta_subst {t a : Term} {σ : Substitution} :
    subst (lam t) σ ⬝ a ⇒* subst t (a ⋆ σ) := by
  show lam (subst t (lift σ)) ⬝ a ⇒* _
  rw [← subst_lift]
  exact WHNorm.appLam

theorem WHNorm.beta4 {t a b c d : Term} :
    lam (lam (lam (lam t))) ⬝ a ⬝ b ⬝ c ⬝ d ⇒* subst t (d ⋆ c ⋆ b ⋆ a ⋆ id) := by
  have h₁ : lam (lam (lam (lam t))) ⬝ a ⇒* subst (lam (lam (lam t))) (a ⋆ id) := by
    have := WHNorm.beta_subst (t := lam (lam (lam t))) (a := a) (σ := id)
    rwa [subst_id] at this
  have h₂ := WHNorm.beta_subst (t := lam (lam t)) (a := b) (σ := a ⋆ id)
  have h₃ := WHNorm.beta_subst (t := lam t) (a := c) (σ := b ⋆ a ⋆ id)
  have h₄ := WHNorm.beta_subst (t := t) (a := d) (σ := c ⋆ b ⋆ a ⋆ id)
  exact ((h₁.appNe.appNe.appNe).trans (h₂.appNe.appNe)).trans (h₃.appNe.trans h₄)

/-! The diagonal term is `D x := succ (E (App x (Quote x)))`, except that we
force the argument of `E` to a numeral with `rect` first: weak-head reduction
never evaluates arguments, and a self-evaluator is only specified on literal
codes. `E`, `App` and `Quote` are passed as arguments (variables 3, 2, 1) so no
closedness assumptions are needed. -/

/-- `fun k _ => E (succ k)` -/
def diagStep : Term := lam (lam (var 5 ⬝ succ (var 1)))

def diagBody : Term := succ (rect (var 3 ⬝ zero) diagStep (var 2 ⬝ var 0 ⬝ (var 1 ⬝ var 0)))

/-- `fun E App Quote x => succ (E (App x (Quote x)))` (forcing the argument). -/
def diagonal : Term := lam (lam (lam (lam diagBody)))

def diag [ReasonableEncoding] (E : Term) : Term :=
  diagonal ⬝ E ⬝ ReasonableEncoding.appT ⬝ ReasonableEncoding.quoteT

theorem diagStep_spec {σ : Substitution} {k acc : Term} :
    subst diagStep σ ⬝ k ⬝ acc ⇒* substVar 3 σ ⬝ succ k := by
  unfold diagStep
  have h₁ := WHNorm.beta_subst (t := lam (var 5 ⬝ succ (var 1))) (a := k) (σ := σ)
  have h₂ := WHNorm.beta_subst (t := var 5 ⬝ succ (var 1)) (a := acc) (σ := k ⋆ σ)
  have e : subst (var 5 ⬝ succ (var 1)) (acc ⋆ k ⋆ σ) = substVar 3 σ ⬝ succ k := by
    simp [subst, substVar]
  rw [e] at h₂
  exact h₁.appNe.trans h₂

theorem diag_force {σ : Substitution} {a : Term} {m : Nat} (ha : a ⇒* numeral m) :
    rect (substVar 3 σ ⬝ zero) (subst diagStep σ) a ⇒* substVar 3 σ ⬝ numeral m := by
  refine (WHNorm.rectNe ha).trans ?_
  cases m with
  | zero => exact WHNorm.step WHRed.rectz WHNorm.refl
  | succ m => exact WHNorm.step WHRed.rects diagStep_spec

/-- The diagonal equation: `D ⌜D⌝ ⇒* succ (E ⌜D ⌜D⌝⌝)`. -/
theorem diag_spec [ReasonableEncoding] (E : Term) :
    diag E ⬝ ⌜diag E⌝ ⇒* succ (E ⬝ ⌜diag E ⬝ ⌜diag E⌝⌝) := by
  obtain ⟨m, hm⟩ := (Encoding.is_val_encode (diag E ⬝ ⌜diag E⌝)).eq_numeral
  have h₁ : diag E ⬝ ⌜diag E⌝ ⇒* subst diagBody
      (⌜diag E⌝ ⋆ ReasonableEncoding.quoteT ⋆ ReasonableEncoding.appT ⋆ E ⋆ id) :=
    WHNorm.beta4
  refine h₁.trans ?_
  have ha : ReasonableEncoding.appT ⬝ ⌜diag E⌝ ⬝ (ReasonableEncoding.quoteT ⬝ ⌜diag E⌝)
      ⇒* numeral m := by
    rw [← hm]
    exact ReasonableEncoding.appT_spec WHNorm.refl (ReasonableEncoding.quoteT_spec WHNorm.refl)
  rw [hm]
  exact WHNorm.succ
    (diag_force (σ := ⌜diag E⌝ ⋆ ReasonableEncoding.quoteT ⋆ ReasonableEncoding.appT ⋆ E ⋆ id) ha)

theorem diagonal_typed {Γ : Ctxt} :
    HasType Γ diagonal ((nat ⟶ nat) ⟶ (nat ⟶ nat ⟶ nat) ⟶ (nat ⟶ nat) ⟶ nat ⟶ nat) :=
  .lam (.lam (.lam (.lam (.succ (.rect
    (.app (.var (n := 3) (by simp)) .zero)
    (.lam (.lam (.app (.var (n := 5) (by simp)) (.succ (.var (n := 1) (by simp))))))
    (.app (.app (.var (n := 2) (by simp)) (.var (n := 0) (by simp)))
      (.app (.var (n := 1) (by simp)) (.var (n := 0) (by simp)))))))))

/-- **There is no well-typed self-evaluator** for any reasonable encoding. -/
theorem no_self_evaluator [ReasonableEncoding] (E : Term) : ¬ SelfEvaluator E := by
  intro ⟨hE, hspec⟩
  have hD : HasType [] (diag E) (nat ⟶ nat) :=
    .app (.app (.app diagonal_typed hE) ReasonableEncoding.appT_typed)
      ReasonableEncoding.quoteT_typed
  have ht : HasType [] (diag E ⬝ ⌜diag E⌝) nat := .app hD (Encoding.is_nat_encode _)
  obtain ⟨n, hn⟩ := normalize ht
  have h : diag E ⬝ ⌜diag E⌝ ⇒* numeral (n + 1) :=
    (diag_spec E).trans (WHNorm.succ (hspec _ n ht hn))
  have := numeral_unique hn h
  omega

/-- In particular, for the Cantor encoding. -/
example (E : Term) : ¬ SelfEvaluator E := no_self_evaluator E
