import PeanoPlaying.Basic
import PeanoPlaying.HA

/-!
# Preliminaries for realizability

Term-level infrastructure used by the realizability judgment:

* parallel substitutions `Nat → Term` (`psubst`) and their algebra;
* System T typing against infinite contexts (`HasTypeF`);
* convertibility (`Conv`) and facts about numerals;
* the translation `tr` of HA terms into T, and standard evaluation `eval`;
* `NatNorm`, weak normalization of closed `nat` terms, and default terms.
-/

namespace Rz

open Term Ty

/-! ## Parallel substitutions as functions

`Basic.lean` represents substitutions as syntax; for realizers it is more
convenient to substitute a whole environment `Nat → Term` at once. -/

/-- `scons a f` maps `0 ↦ a` and `k + 1 ↦ f k`. -/
def scons {α : Type} (a : α) (f : Nat → α) : Nat → α
  | 0 => a
  | k + 1 => f k

@[simp] theorem scons_zero {α : Type} (a : α) (f : Nat → α) : scons a f 0 = a := rfl
@[simp] theorem scons_succ {α : Type} (a : α) (f : Nat → α) (k : Nat) :
    scons a f (k + 1) = f k := rfl

/-- Weakening by one variable. -/
def sh (t : Term) : Term := substRen t .shift

@[simp] theorem sh_var (k : Nat) : sh (var k) = var (k + 1) := rfl

/-- Lift a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term := scons (var 0) (fun k => sh (σ k))

@[simp] theorem up_zero (σ : Nat → Term) : up σ 0 = var 0 := rfl
@[simp] theorem up_succ (σ : Nat → Term) (k : Nat) : up σ (k + 1) = sh (σ k) := rfl

/-- Simultaneous substitution of `σ k` for every variable `k`. -/
def psubst (σ : Nat → Term) : Term → Term
  | var k => σ k
  | app t u => app (psubst σ t) (psubst σ u)
  | lam t => lam (psubst (up σ) t)
  | zero => zero
  | succ t => succ (psubst σ t)
  | rect z s t => rect (psubst σ z) (psubst σ s) (psubst σ t)
  | pair a b => pair (psubst σ a) (psubst σ b)
  | fst t => fst (psubst σ t)
  | snd t => snd (psubst σ t)

theorem psubst_ren (t : Term) : ∀ (σ : Nat → Term) (τ : Renaming),
    psubst σ (substRen t τ) = psubst (fun k => σ (renVar k τ)) t := by
  induction t with
  | var k => intro σ τ; rfl
  | lam t ih =>
    intro σ τ
    simp only [substRen, psubst, ih]
    congr 2
    funext k
    cases k <;> simp [liftRen, renVar]
  | _ => intro σ τ; simp_all [substRen, psubst]

theorem ren_psubst (t : Term) : ∀ (σ : Nat → Term) (τ : Renaming),
    substRen (psubst σ t) τ = psubst (fun k => substRen (σ k) τ) t := by
  induction t with
  | var k => intro σ τ; rfl
  | lam t ih =>
    intro σ τ
    simp only [substRen, psubst, ih]
    congr 2
    funext k
    cases k with
    | zero => simp [substRen, liftRen, renVar]
    | succ k =>
      simp only [up_succ, sh, substRen_comp]
      apply ren_congr
      intro m
      simp [renVar, liftRen]
  | _ => intro σ τ; simp_all [substRen, psubst]

theorem psubst_psubst (t : Term) : ∀ (σ τ : Nat → Term),
    psubst τ (psubst σ t) = psubst (fun k => psubst τ (σ k)) t := by
  induction t with
  | var k => intro σ τ; rfl
  | lam t ih =>
    intro σ τ
    simp only [psubst, ih]
    congr 2
    funext k
    cases k with
    | zero => rfl
    | succ k =>
      simp only [up_succ, sh, psubst_ren, ren_psubst]
      rfl
  | _ => intro σ τ; simp_all [psubst]

theorem psubst_var (t : Term) : psubst var t = t := by
  have hup : up var = var := by funext k; cases k <;> rfl
  induction t with
  | lam t ih => simp only [psubst, hup, ih]
  | _ => simp_all [psubst]

/-- Basic's syntactic substitutions are a special case. -/
theorem subst_eq_psubst (t : Term) : ∀ s : Substitution,
    subst t s = psubst (fun k => substVar k s) t := by
  induction t with
  | var k => intro s; rfl
  | lam t ih =>
    intro s
    simp only [subst, psubst, ih]
    congr 2
    funext k
    cases k with
    | zero => simp [lift, substVar]
    | succ k => simp [lift, substVar, sh]
  | _ => intro s; simp_all [subst, psubst]

@[simp] theorem psubst_sh_scons (a : Term) (σ : Nat → Term) (t : Term) :
    psubst (scons a σ) (sh t) = psubst σ t := by
  simp only [sh, psubst_ren]
  rfl

theorem psubst_up_sh (σ : Nat → Term) (t : Term) :
    psubst (up σ) (sh t) = sh (psubst σ t) := by
  simp only [sh, psubst_ren, ren_psubst]
  rfl

theorem psubst_scons_var (σ : Nat → Term) (a t : Term) :
    psubst σ (psubst (scons a var) t) = psubst (scons (psubst σ a) σ) t := by
  rw [psubst_psubst]
  congr 1
  funext k
  cases k <;> rfl

/-- β-reduction in terms of `psubst`. -/
theorem subst_up_beta (σ : Nat → Term) (t u : Term) :
    subst (psubst (up σ) t) (u ⋆ id) = psubst (scons u σ) t := by
  rw [subst_eq_psubst, psubst_psubst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [up_succ, sh, psubst_ren]
    have : (fun j => substVar (renVar j Renaming.shift) (u ⋆ id)) = var := by
      funext j; simp [renVar, substVar]
    rw [this, psubst_var]
    rfl

theorem red_beta_psubst (σ : Nat → Term) (t u : Term) :
    Red (app (psubst σ (lam t)) u) (psubst (scons u σ) t) := by
  have h := Red.beta (t := psubst (up σ) t) (u := u)
  rwa [subst_up_beta] at h

theorem red_beta2_psubst (σ : Nat → Term) (t a b : Term) :
    app (app (psubst σ (lam (lam t))) a) b ⟶* psubst (scons b (scons a σ)) t :=
  .step (.appL (red_beta_psubst σ (lam t) a)) (.single (red_beta_psubst _ t b))

theorem red_beta2 (t a b : Term) :
    app (app (lam (lam t)) a) b ⟶* psubst (scons b (scons a var)) t := by
  have h := red_beta2_psubst var t a b
  rwa [psubst_var] at h

theorem red_beta3 (t a b c : Term) :
    app (app (app (lam (lam (lam t))) a) b) c ⟶*
      psubst (scons c (scons b (scons a var))) t := by
  have h₁ : Red (app (lam (lam (lam t))) a) (psubst (scons a var) (lam (lam t))) := by
    have := red_beta_psubst var (lam (lam t)) a
    rwa [psubst_var] at this
  exact .step (.appL (.appL h₁)) (red_beta2_psubst _ t b c)

/-! ## Typing with infinite contexts

Open realizers live in a context with one variable per hypothesis followed by
one `nat` variable per HA variable, so we type them against `Nat → Ty`. -/

inductive HasTypeF : (Nat → Ty) → Term → Ty → Prop where
| var : HasTypeF Γ (var n) (Γ n)
| app : HasTypeF Γ t (A ⟶ B) → HasTypeF Γ u A → HasTypeF Γ (app t u) B
| lam : HasTypeF (scons A Γ) t B → HasTypeF Γ (lam t) (A ⟶ B)
| zero : HasTypeF Γ zero nat
| succ : HasTypeF Γ t nat → HasTypeF Γ (succ t) nat
| rect : HasTypeF Γ z A → HasTypeF Γ s (nat ⟶ A ⟶ A) → HasTypeF Γ t nat →
    HasTypeF Γ (rect z s t) A
| pair : HasTypeF Γ a A → HasTypeF Γ b B → HasTypeF Γ (pair a b) (A ⊗ B)
| fst : HasTypeF Γ t (A ⊗ B) → HasTypeF Γ (fst t) A
| snd : HasTypeF Γ t (A ⊗ B) → HasTypeF Γ (snd t) B

theorem HasTypeF.var' {Γ : Nat → Ty} {n : Nat} {A : Ty} (h : Γ n = A) :
    HasTypeF Γ (Term.var n) A := h ▸ HasTypeF.var

theorem HasTypeF.ren {Γ : Nat → Ty} {t : Term} {A : Ty} (h : HasTypeF Γ t A) :
    ∀ (Δ : Nat → Ty) (τ : Renaming), (∀ k, Δ (renVar k τ) = Γ k) →
      HasTypeF Δ (substRen t τ) A := by
  induction h with
  | var => intro Δ τ hτ; exact .var' (hτ _)
  | app _ _ ih₁ ih₂ => intro Δ τ hτ; exact .app (ih₁ Δ τ hτ) (ih₂ Δ τ hτ)
  | lam _ ih =>
    intro Δ τ hτ
    refine .lam (ih _ _ ?_)
    intro k
    cases k <;> simp [liftRen, renVar, hτ]
  | zero => intros; exact .zero
  | succ _ ih => intro Δ τ hτ; exact .succ (ih Δ τ hτ)
  | rect _ _ _ ihz ihs iht => intro Δ τ hτ; exact .rect (ihz Δ τ hτ) (ihs Δ τ hτ) (iht Δ τ hτ)
  | pair _ _ iha ihb => intro Δ τ hτ; exact .pair (iha Δ τ hτ) (ihb Δ τ hτ)
  | fst _ ih => intro Δ τ hτ; exact .fst (ih Δ τ hτ)
  | snd _ ih => intro Δ τ hτ; exact .snd (ih Δ τ hτ)

theorem HasTypeF.sh {Γ : Nat → Ty} {t : Term} {A B : Ty} (h : HasTypeF Γ t A) :
    HasTypeF (scons B Γ) (Rz.sh t) A :=
  h.ren _ _ (fun _ => rfl)

theorem HasTypeF.psubst {Γ : Nat → Ty} {t : Term} {A : Ty} (h : HasTypeF Γ t A) :
    ∀ (Δ : Nat → Ty) (σ : Nat → Term), (∀ k, HasTypeF Δ (σ k) (Γ k)) →
      HasTypeF Δ (Rz.psubst σ t) A := by
  induction h with
  | var => intro Δ σ hσ; exact hσ _
  | app _ _ ih₁ ih₂ => intro Δ σ hσ; exact .app (ih₁ Δ σ hσ) (ih₂ Δ σ hσ)
  | lam _ ih =>
    intro Δ σ hσ
    refine .lam (ih _ _ ?_)
    intro k
    cases k with
    | zero => exact .var
    | succ k => exact (hσ k).sh
  | zero => intros; exact .zero
  | succ _ ih => intro Δ σ hσ; exact .succ (ih Δ σ hσ)
  | rect _ _ _ ihz ihs iht => intro Δ σ hσ; exact .rect (ihz Δ σ hσ) (ihs Δ σ hσ) (iht Δ σ hσ)
  | pair _ _ iha ihb => intro Δ σ hσ; exact .pair (iha Δ σ hσ) (ihb Δ σ hσ)
  | fst _ ih => intro Δ σ hσ; exact .fst (ih Δ σ hσ)
  | snd _ ih => intro Δ σ hσ; exact .snd (ih Δ σ hσ)

/-- Weakening for Basic's list contexts. -/
theorem _root_.HasType.ren {Γ : Ctxt} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∀ (Δ : Ctxt) (τ : Renaming),
      (∀ n (hn : n < Γ.length), ∃ h' : renVar n τ < Δ.length, Δ[renVar n τ] = Γ[n]) →
      HasType Δ (substRen t τ) A := by
  induction h with
  | var hn =>
    intro Δ τ hτ
    obtain ⟨h', e⟩ := hτ _ hn
    simp only [substRen]
    rw [← e]
    exact HasType.var h'
  | app _ _ ih₁ ih₂ => intro Δ τ hτ; exact .app (ih₁ Δ τ hτ) (ih₂ Δ τ hτ)
  | lam _ ih =>
    intro Δ τ hτ
    refine .lam (ih _ _ ?_)
    intro n hn
    cases n with
    | zero => exact ⟨by simp [liftRen, renVar], by simp [liftRen, renVar]⟩
    | succ n =>
      obtain ⟨h', e⟩ := hτ n (by simpa using hn)
      exact ⟨by simpa [liftRen, renVar] using h', by simpa [liftRen, renVar] using e⟩
  | zero => intros; exact .zero
  | succ _ ih => intro Δ τ hτ; exact .succ (ih Δ τ hτ)
  | rect _ _ _ ihz ihs iht => intro Δ τ hτ; exact .rect (ihz Δ τ hτ) (ihs Δ τ hτ) (iht Δ τ hτ)
  | pair _ _ iha ihb => intro Δ τ hτ; exact .pair (iha Δ τ hτ) (ihb Δ τ hτ)
  | fst _ ih => intro Δ τ hτ; exact .fst (ih Δ τ hτ)
  | snd _ ih => intro Δ τ hτ; exact .snd (ih Δ τ hτ)

theorem _root_.HasType.sh {Γ : Ctxt} {t : Term} {A B : Ty} (h : HasType Γ t A) :
    HasType (B :: Γ) (Rz.sh t) A :=
  h.ren _ _ (fun n hn => ⟨by simpa [renVar] using hn, by simp [renVar]⟩)

/-- Instantiating an open, `HasTypeF`-typed term with well-typed terms. -/
theorem HasTypeF.psubst_list {Γ : Nat → Ty} {t : Term} {A : Ty} (h : HasTypeF Γ t A) :
    ∀ (Δ : Ctxt) (σ : Nat → Term), (∀ k, HasType Δ (σ k) (Γ k)) →
      HasType Δ (Rz.psubst σ t) A := by
  induction h with
  | var => intro Δ σ hσ; exact hσ _
  | app _ _ ih₁ ih₂ => intro Δ σ hσ; exact .app (ih₁ Δ σ hσ) (ih₂ Δ σ hσ)
  | lam _ ih =>
    intro Δ σ hσ
    refine .lam (ih _ _ ?_)
    intro k
    cases k with
    | zero => exact HasType.var (by simp)
    | succ k => exact (hσ k).sh
  | zero => intros; exact .zero
  | succ _ ih => intro Δ σ hσ; exact .succ (ih Δ σ hσ)
  | rect _ _ _ ihz ihs iht => intro Δ σ hσ; exact .rect (ihz Δ σ hσ) (ihs Δ σ hσ) (iht Δ σ hσ)
  | pair _ _ iha ihb => intro Δ σ hσ; exact .pair (iha Δ σ hσ) (ihb Δ σ hσ)
  | fst _ ih => intro Δ σ hσ; exact .fst (ih Δ σ hσ)
  | snd _ ih => intro Δ σ hσ; exact .snd (ih Δ σ hσ)

/-- Closed terms are typed in any context. -/
theorem _root_.HasType.toF {t : Term} {A : Ty} (h : HasType [] t A) (Γ : Nat → Ty) :
    HasTypeF Γ t A := by
  suffices ∀ (L : Ctxt) (t : Term) (A : Ty), HasType L t A →
      ∀ Γ : Nat → Ty, (∀ n (hn : n < L.length), Γ n = L[n]) → HasTypeF Γ t A from
    this [] t A h Γ (fun _ hn => absurd hn (Nat.not_lt_zero _))
  intro L t A h
  induction h with
  | var hn => intro Γ hΓ; exact .var' (hΓ _ hn)
  | app _ _ ih₁ ih₂ => intro Γ hΓ; exact .app (ih₁ Γ hΓ) (ih₂ Γ hΓ)
  | lam _ ih =>
    intro Γ hΓ
    refine .lam (ih _ ?_)
    intro n hn
    cases n with
    | zero => rfl
    | succ n => simpa using hΓ n (by simpa using hn)
  | zero => intros; exact .zero
  | succ _ ih => intro Γ hΓ; exact .succ (ih Γ hΓ)
  | rect _ _ _ ihz ihs iht => intro Γ hΓ; exact .rect (ihz Γ hΓ) (ihs Γ hΓ) (iht Γ hΓ)
  | pair _ _ iha ihb => intro Γ hΓ; exact .pair (iha Γ hΓ) (ihb Γ hΓ)
  | fst _ ih => intro Γ hΓ; exact .fst (ih Γ hΓ)
  | snd _ ih => intro Γ hΓ; exact .snd (ih Γ hΓ)

/-! ## Convertibility -/

/-- Two terms are convertible when they have a common reduct. -/
def Conv (a b : Term) : Prop := ∃ w, a ⟶* w ∧ b ⟶* w

theorem Conv.refl (a : Term) : Conv a a := ⟨a, .refl, .refl⟩

theorem Conv.symm {a b : Term} (h : Conv a b) : Conv b a :=
  let ⟨w, h₁, h₂⟩ := h; ⟨w, h₂, h₁⟩

theorem Conv.trans {a b c : Term} (h₁ : Conv a b) (h₂ : Conv b c) : Conv a c := by
  obtain ⟨w₁, ha, hb₁⟩ := h₁
  obtain ⟨w₂, hb₂, hc⟩ := h₂
  obtain ⟨w, h₁w, h₂w⟩ := red_confluent hb₁ hb₂
  exact ⟨w, ha.trans h₁w, hc.trans h₂w⟩

theorem Conv.of_red {a b : Term} (h : a ⟶* b) : Conv a b := ⟨b, h, .refl⟩

theorem Conv.app {t t' u u' : Term} (ht : Conv t t') (hu : Conv u u') :
    Conv (app t u) (app t' u') :=
  let ⟨w₁, h₁, h₁'⟩ := ht; let ⟨w₂, h₂, h₂'⟩ := hu
  ⟨_, h₁.app h₂, h₁'.app h₂'⟩

theorem Conv.succ {t t' : Term} (h : Conv t t') : Conv (succ t) (succ t') :=
  let ⟨_, h₁, h₂⟩ := h; ⟨_, h₁.succ, h₂.succ⟩

theorem Conv.fst {t t' : Term} (h : Conv t t') : Conv (fst t) (fst t') :=
  let ⟨_, h₁, h₂⟩ := h; ⟨_, h₁.fst, h₂.fst⟩

theorem Conv.snd {t t' : Term} (h : Conv t t') : Conv (snd t) (snd t') :=
  let ⟨_, h₁, h₂⟩ := h; ⟨_, h₁.snd, h₂.snd⟩

theorem Conv.rect {z z' s s' t t' : Term} (hz : Conv z z') (hs : Conv s s') (ht : Conv t t') :
    Conv (rect z s t) (rect z' s' t') :=
  let ⟨_, h₁, h₁'⟩ := hz; let ⟨_, h₂, h₂'⟩ := hs; let ⟨_, h₃, h₃'⟩ := ht
  ⟨_, RedStar.rect h₁ h₂ h₃, RedStar.rect h₁' h₂' h₃'⟩

theorem red_numeral_inv : ∀ {n : Nat} {w : Term}, Red (numeral n) w → False
  | 0, _, h => by cases h
  | n + 1, _, h => by
    change Red (Term.succ (numeral n)) _ at h
    cases h with
    | succ h => exact red_numeral_inv h

theorem redStar_numeral_inv {n : Nat} {w : Term} (h : numeral n ⟶* w) : w = numeral n := by
  cases h with
  | refl => rfl
  | step r _ => exact (red_numeral_inv r).elim

/-- Numerals are normal, so converting to a numeral means reducing to it. -/
theorem Conv.to_numeral {t : Term} {n : Nat} (h : Conv t (numeral n)) : t ⟶* numeral n := by
  obtain ⟨w, h₁, h₂⟩ := h
  rw [redStar_numeral_inv h₂] at h₁
  exact h₁

theorem Conv.numeral_inj {n m : Nat} (h : Conv (numeral n) (numeral m)) : n = m :=
  _root_.numeral_inj (redStar_numeral_inv h.to_numeral).symm

theorem redStar_succ_inv {t w : Term} (h : succ t ⟶* w) : ∃ t', w = succ t' ∧ t ⟶* t' := by
  generalize e : succ t = s at h
  induction h generalizing t with
  | refl => exact ⟨t, e.symm, .refl⟩
  | step r _ ih =>
    subst e
    cases r with
    | succ r =>
      obtain ⟨t', rfl, h⟩ := ih rfl
      exact ⟨t', rfl, .step r h⟩

theorem Conv.succ_inj {a b : Term} (h : Conv (Term.succ a) (Term.succ b)) : Conv a b := by
  obtain ⟨w, h₁, h₂⟩ := h
  obtain ⟨a', rfl, ha⟩ := redStar_succ_inv h₁
  obtain ⟨b', e, hb⟩ := redStar_succ_inv h₂
  cases e
  exact ⟨a', ha, hb⟩

theorem not_conv_zero_succ {a : Term} : ¬ Conv zero (succ a) := by
  intro ⟨w, h₁, h₂⟩
  have := redStar_numeral_inv (n := 0) h₁
  obtain ⟨_, rfl, _⟩ := redStar_succ_inv h₂
  cases this

/-! ## Translating arithmetic terms -/

/-- `fun x _ acc => acc + x` (recursion on the second argument of `+`). -/
def mulStep : Term := lam (lam (lam (rect (var 0) addStep (var 2))))

/-- The T-term denoted by an HA term, with HA variable `k` read as `ρ k`.
Addition and multiplication recurse on their second argument, as the
defining axioms of HA do. -/
def tr (ρ : Nat → Term) : HA.Tm → Term
  | .var k => ρ k
  | .zero => zero
  | .succ t => succ (tr ρ t)
  | .add t u => rect (tr ρ t) addStep (tr ρ u)
  | .mul t u => rect zero (app mulStep (tr ρ t)) (tr ρ u)

@[simp] theorem psubst_addStep (σ : Nat → Term) : psubst σ addStep = addStep := rfl
@[simp] theorem psubst_mulStep (σ : Nat → Term) : psubst σ mulStep = mulStep := rfl

theorem psubst_tr (σ ρ : Nat → Term) (a : HA.Tm) :
    psubst σ (tr ρ a) = tr (fun k => psubst σ (ρ k)) a := by
  induction a <;> simp_all [tr, psubst]

theorem tr_subst (ρ : Nat → Term) (σ : Nat → HA.Tm) (a : HA.Tm) :
    tr ρ (a.subst σ) = tr (fun k => tr ρ (σ k)) a := by
  induction a <;> simp_all [tr, HA.Tm.subst]

theorem tr_up (a : Term) (ρ : Nat → Term) (σ : Nat → HA.Tm) :
    (fun k => tr (scons a ρ) (HA.Tm.up σ k)) = scons a (fun k => tr ρ (σ k)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show tr (scons a ρ) ((σ k).subst HA.Tm.shift) = tr ρ (σ k)
    rw [tr_subst]
    rfl

theorem tr_typed {ρ : Nat → Term} (hρ : ∀ k, HasType [] (ρ k) nat) :
    ∀ a, HasType [] (tr ρ a) nat
  | .var k => hρ k
  | .zero => .zero
  | .succ t => .succ (tr_typed hρ t)
  | .add t u => .rect (tr_typed hρ t) addStep_typed (tr_typed hρ u)
  | .mul t u =>
    .rect .zero
      (.app (.lam (.lam (.lam (.rect (.var (n := 0) (by simp)) addStep_typed
        (.var (n := 2) (by simp)))))) (tr_typed hρ t))
      (tr_typed hρ u)

theorem tr_typedF {Γ : Nat → Ty} {ρ : Nat → Term} (hρ : ∀ k, HasTypeF Γ (ρ k) nat) :
    ∀ a, HasTypeF Γ (tr ρ a) nat
  | .var k => hρ k
  | .zero => .zero
  | .succ t => .succ (tr_typedF hρ t)
  | .add t u => .rect (tr_typedF hρ t) (addStep_typed (Γ := []).toF Γ) (tr_typedF hρ u)
  | .mul t u =>
    .rect .zero (.app (HasType.toF (t := mulStep) (A := nat ⟶ nat ⟶ nat ⟶ nat)
        (.lam (.lam (.lam (.rect (.var (n := 0) (by simp)) addStep_typed
          (.var (n := 2) (by simp)))))) Γ) (tr_typedF hρ t))
      (tr_typedF hρ u)

/-- Pointwise convertible environments. -/
def EnvConv (ρ ρ' : Nat → Term) : Prop := ∀ k, Conv (ρ k) (ρ' k)

theorem EnvConv.scons {ρ ρ' : Nat → Term} (h : EnvConv ρ ρ') (a : Term) :
    EnvConv (scons a ρ) (scons a ρ') := by
  intro k; cases k
  · exact .refl a
  · exact h _

theorem tr_conv {ρ ρ' : Nat → Term} (h : EnvConv ρ ρ') : ∀ a, Conv (tr ρ a) (tr ρ' a)
  | .var k => h k
  | .zero => .refl _
  | .succ t => (tr_conv h t).succ
  | .add t u => .rect (tr_conv h t) (.refl _) (tr_conv h u)
  | .mul t u => .rect (.refl _) (.app (.refl _) (tr_conv h t)) (tr_conv h u)

/-! ### The defining equations hold up to reduction, for arbitrary terms -/

theorem red_add_zero (a : Term) : rect a addStep zero ⟶* a := .single .rectz

theorem red_add_succ (a b : Term) :
    rect a addStep (succ b) ⟶* succ (rect a addStep b) :=
  .step .rects (red_beta2 (succ (var 0)) _ _)

theorem red_mul_zero (a : Term) : rect zero (app mulStep a) zero ⟶* zero := .single .rectz

theorem red_mul_succ (a b : Term) :
    rect zero (app mulStep a) (succ b) ⟶*
      rect (rect zero (app mulStep a) b) addStep a :=
  .step .rects (red_beta3 (rect (var 0) addStep (var 2)) _ _ _)

/-! ### Standard values -/

/-- Evaluation of HA terms in the standard model. -/
def eval (e : Nat → Nat) : HA.Tm → Nat
  | .var k => e k
  | .zero => 0
  | .succ t => eval e t + 1
  | .add t u => eval e t + eval e u
  | .mul t u => eval e t * eval e u

theorem red_add_numeral {a b : Term} {n m : Nat} (ha : a ⟶* numeral n) (hb : b ⟶* numeral m) :
    rect a addStep b ⟶* numeral (n + m) := by
  refine (RedStar.rect ha .refl hb).trans ?_
  clear ha hb
  induction m with
  | zero => exact .single .rectz
  | succ m ih => exact (red_add_succ _ _).trans ih.succ

theorem red_mul_numeral {a b : Term} {n m : Nat} (ha : a ⟶* numeral n) (hb : b ⟶* numeral m) :
    rect zero (app mulStep a) b ⟶* numeral (n * m) := by
  refine (RedStar.rect .refl .refl hb).trans ?_
  clear hb
  induction m with
  | zero => exact .single .rectz
  | succ m ih => exact (red_mul_succ _ _).trans (red_add_numeral ih ha)

theorem tr_eval (e : Nat → Nat) : ∀ a, tr (fun k => numeral (e k)) a ⟶* numeral (eval e a)
  | .var _ => .refl
  | .zero => .refl
  | .succ t => (tr_eval e t).succ
  | .add t u => red_add_numeral (tr_eval e t) (tr_eval e u)
  | .mul t u => red_mul_numeral (tr_eval e t) (tr_eval e u)

/-! ## Normalization and default terms -/

/-- Weak normalization of closed terms of type `nat`. -/
def NatNorm : Prop := ∀ t, HasType [] t nat → ∃ n, t ⟶* numeral n

/-- `Basic.lean` proves it, via computability. -/
theorem natNorm : NatNorm := fun _ h =>
  let ⟨n, hn⟩ := normalize h; ⟨n, whnorm_redStar hn⟩

/-- A closed inhabitant of every type. -/
def dflt : Ty → Term
  | .nat => zero
  | .arrow _ B => lam (dflt B)
  | .prod A B => pair (dflt A) (dflt B)

theorem dflt_typed : ∀ (A : Ty) {Γ : Ctxt}, HasType Γ (dflt A) A
  | .nat, _ => .zero
  | .arrow _ B, _ => .lam (dflt_typed B)
  | .prod A B, _ => .pair (dflt_typed A) (dflt_typed B)

end Rz
