import PeanoPlaying.Prelim

/-!
# An inductive realizability judgment

Realizability defined by recursion on formulas gives each
formula its own predicate, and quantifier complexity grows with the
formula. Statements that quantify over *all* proofs, such as
`NatNorm → Con(HA)`, therefore cannot be stated inside HA.

Here realizability is a single inductively defined relation `D ⊢ t ⊩ A` (`RJ`), a
Curry-style typing judgment on T-terms. Every premise is itself inductive or
Σ₁ (convertibility, typing), so the whole relation is Σ₁-definable.

* Formulas `TF` have T-terms as atoms. Free variables are T-variables, and
  β-reduction instantiates them with arbitrary terms of type `nat` (such as
  `fst p` in ∃-elimination).
* `⊥` is `0 = 1`. An equation is introduced only by the realizer `zero`,
  under the side condition that the two sides are convertible. Equations are
  eliminated by `rect`, which forces the proof before the result is used.

The metatheory proved here:
* substitution (`RJ.subst`),
* subject reduction for full reduction (`RJ.red`, `RJ.redStar`),
* erasure to System T typing (`RJ.erase`),
* no numeral realizes `0 = 1` (`no_numeral_bot`).
-/

namespace Rz

open Term Ty

/-! ## More on substitutions -/

/-- The weakening substitution `k ↦ k + 1`. -/
def wk : Nat → Term := fun k => var (k + 1)

@[simp] theorem wk_apply (k : Nat) : wk k = var (k + 1) := rfl

theorem sh_eq (t : Term) : sh t = psubst wk t := by
  have h := psubst_ren t var .shift
  rw [psubst_var] at h
  exact h

theorem up_comp (σ τ : Nat → Term) :
    (fun k => psubst (up τ) (up σ k)) = up (fun k => psubst τ (σ k)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => exact psubst_up_sh τ (σ k)

theorem up_var : up var = var := by funext k; cases k <;> rfl

theorem psubst_wk_scons (a : Term) (σ : Nat → Term) (t : Term) :
    psubst (scons a σ) (psubst wk t) = psubst σ t := by
  rw [← sh_eq]; exact psubst_sh_scons a σ t

@[simp] theorem psubst_numeral (σ : Nat → Term) (n : Nat) : psubst σ (numeral n) = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numeral, psubst, ih]

theorem psubst_dflt : ∀ (A : Ty) (σ : Nat → Term), psubst σ (dflt A) = dflt A
  | .nat, _ => rfl
  | .arrow _ B, σ => by simp only [dflt, psubst, psubst_dflt B]
  | .prod A B, σ => by simp only [dflt, psubst, psubst_dflt A, psubst_dflt B]

theorem subst_single (t u : Term) : subst t (u ⋆ id) = psubst (scons u var) t := by
  rw [subst_eq_psubst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k => simp [substVar, renVar]

theorem _root_.Red.psubst {t t' : Term} (h : Red t t') : ∀ σ, Red (psubst σ t) (psubst σ t') := by
  induction h with
  | beta =>
    intro σ
    rw [subst_single, psubst_scons_var]
    exact red_beta_psubst σ _ _
  | rectz => intro σ; exact .rectz
  | rects => intro σ; exact .rects
  | appL _ ih => intro σ; exact .appL (ih σ)
  | appR _ ih => intro σ; exact .appR (ih σ)
  | lam _ ih => intro σ; exact .lam (ih _)
  | succ _ ih => intro σ; exact .succ (ih σ)
  | rectZ _ ih => intro σ; exact .rectZ (ih σ)
  | rectS _ ih => intro σ; exact .rectS (ih σ)
  | rectT _ ih => intro σ; exact .rectT (ih σ)
  | fstβ => intro σ; exact .fstβ
  | sndβ => intro σ; exact .sndβ
  | pairL _ ih => intro σ; exact .pairL (ih σ)
  | pairR _ ih => intro σ; exact .pairR (ih σ)
  | fst _ ih => intro σ; exact .fst (ih σ)
  | snd _ ih => intro σ; exact .snd (ih σ)

theorem _root_.RedStar.psubst {t t' : Term} (h : t ⟶* t') (σ : Nat → Term) :
    psubst σ t ⟶* psubst σ t' := by
  induction h with
  | refl => exact .refl
  | step r _ ih => exact .step (r.psubst σ) ih

theorem Conv.psubst {a b : Term} (h : Conv a b) (σ : Nat → Term) :
    Conv (Rz.psubst σ a) (Rz.psubst σ b) :=
  let ⟨_, h₁, h₂⟩ := h; ⟨_, h₁.psubst σ, h₂.psubst σ⟩

theorem psubst_redStar_env (t : Term) : ∀ σ σ' : Nat → Term, (∀ k, σ k ⟶* σ' k) →
    psubst σ t ⟶* psubst σ' t := by
  induction t with
  | var k => intro σ σ' h; exact h k
  | lam t ih =>
    intro σ σ' h
    refine (ih _ _ ?_).lam
    intro k
    cases k with
    | zero => exact .refl
    | succ k => simpa only [up_succ, sh_eq] using (h k).psubst wk
  | app t u iht ihu => intro σ σ' h; exact (iht σ σ' h).app (ihu σ σ' h)
  | zero => intros; exact .refl
  | succ t ih => intro σ σ' h; exact (ih σ σ' h).succ
  | rect z s t ihz ihs iht => intro σ σ' h; exact RedStar.rect (ihz σ σ' h) (ihs σ σ' h) (iht σ σ' h)
  | pair a b iha ihb => intro σ σ' h; exact (iha σ σ' h).pair (ihb σ σ' h)
  | fst t ih => intro σ σ' h; exact (ih σ σ' h).fst
  | snd t ih => intro σ σ' h; exact (ih σ σ' h).snd

/-- Subject reduction for System T typing. -/
theorem HasTypeF.red {Γ : Nat → Ty} {t : Term} {A : Ty} (h : HasTypeF Γ t A) :
    ∀ {t'}, Red t t' → HasTypeF Γ t' A := by
  induction h with
  | var => intro t' r; cases r
  | app ht hu ih₁ ih₂ =>
    intro t' r
    cases r with
    | beta =>
      cases ht with
      | lam hb =>
        rw [subst_single]
        exact hb.psubst _ _ (fun k => by
          cases k with
          | zero => exact hu
          | succ k => exact .var)
    | appL r => exact .app (ih₁ r) hu
    | appR r => exact .app ht (ih₂ r)
  | lam _ ih => intro t' r; cases r with | lam r => exact .lam (ih r)
  | zero => intro t' r; cases r
  | succ _ ih => intro t' r; cases r with | succ r => exact .succ (ih r)
  | rect hz hs hn ihz ihs ihn =>
    intro t' r
    cases r with
    | rectz => exact hz
    | rects => cases hn with | succ hn => exact .app (.app hs hn) (.rect hz hs hn)
    | rectZ r => exact .rect (ihz r) hs hn
    | rectS r => exact .rect hz (ihs r) hn
    | rectT r => exact .rect hz hs (ihn r)
  | pair _ _ iha ihb =>
    intro t' r
    cases r with
    | pairL r => exact .pair (iha r) ‹_›
    | pairR r => exact .pair ‹_› (ihb r)
  | fst ht ih =>
    intro t' r
    cases r with
    | fstβ => cases ht with | pair ha _ => exact ha
    | fst r => exact .fst (ih r)
  | snd ht ih =>
    intro t' r
    cases r with
    | sndβ => cases ht with | pair _ hb => exact hb
    | snd r => exact .snd (ih r)

/-! ## Formulas over T-terms -/

inductive TF where
  | eq : Term → Term → TF
  | and : TF → TF → TF
  | imp : TF → TF → TF
  | ex : TF → TF
  | all : TF → TF

namespace TF

def subst (σ : Nat → Term) : TF → TF
  | .eq a b => .eq (psubst σ a) (psubst σ b)
  | .and A B => .and (A.subst σ) (B.subst σ)
  | .imp A B => .imp (A.subst σ) (B.subst σ)
  | .ex A => .ex (A.subst (up σ))
  | .all A => .all (A.subst (up σ))

theorem subst_subst (A : TF) : ∀ σ τ : Nat → Term,
    (A.subst σ).subst τ = A.subst (fun k => psubst τ (σ k)) := by
  induction A with
  | eq a b => intro σ τ; simp only [subst, psubst_psubst]
  | and A B ihA ihB => intro σ τ; simp only [subst, ihA, ihB]
  | imp A B ihA ihB => intro σ τ; simp only [subst, ihA, ihB]
  | ex A ih => intro σ τ; simp only [subst, ih, up_comp]
  | all A ih => intro σ τ; simp only [subst, ih, up_comp]

theorem subst_var (A : TF) : A.subst var = A := by
  induction A with
  | eq a b => simp only [subst, psubst_var]
  | and A B ihA ihB => simp only [subst, ihA, ihB]
  | imp A B ihA ihB => simp only [subst, ihA, ihB]
  | ex A ih => simp only [subst, up_var, ih]
  | all A ih => simp only [subst, up_var, ih]

/-- Substitute `a` for variable `0`. -/
def inst (A : TF) (a : Term) : TF := A.subst (scons a var)

/-- Falsity is `0 = 1`. -/
def bot : TF := .eq zero (succ zero)

@[simp] theorem bot_subst (σ : Nat → Term) : bot.subst σ = bot := rfl

/-- `A(x) ↦ A(S x)` for the variable `0`. -/
def succσ : Nat → Term := scons (succ (var 0)) wk

/-- The type of realizers. -/
def ty : TF → Ty
  | .eq _ _ => nat
  | .and A B => A.ty ⊗ B.ty
  | .imp A B => A.ty ⟶ B.ty
  | .ex A => nat ⊗ A.ty
  | .all A => nat ⟶ A.ty

@[simp] theorem ty_subst (A : TF) : ∀ σ, (A.subst σ).ty = A.ty := by
  induction A <;> intro σ <;> simp_all [subst, ty]

theorem subst_wk_scons (A : TF) (a : Term) (σ : Nat → Term) :
    (A.subst wk).subst (scons a σ) = A.subst σ := by
  rw [subst_subst]; rfl

theorem wk_inst (A : TF) (a : Term) : (A.subst wk).inst a = A := by
  rw [inst, subst_wk_scons, subst_var]

theorem wk_up (A : TF) (σ : Nat → Term) : (A.subst wk).subst (up σ) = (A.subst σ).subst wk := by
  rw [subst_subst, subst_subst]
  congr 1
  funext k
  exact sh_eq (σ k)

theorem inst_subst (A : TF) (a : Term) (σ : Nat → Term) :
    (A.inst a).subst σ = (A.subst (up σ)).inst (psubst σ a) := by
  rw [inst, inst, subst_subst, subst_subst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show σ k = psubst (scons (psubst σ a) var) (sh (σ k))
    rw [psubst_sh_scons, psubst_var]

theorem succ_up (A : TF) (σ : Nat → Term) :
    (A.subst succσ).subst (up σ) = (A.subst (up σ)).subst succσ := by
  rw [subst_subst, subst_subst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show sh (σ k) = psubst (scons (succ (var 0)) wk) (sh (σ k))
    rw [psubst_sh_scons, sh_eq]

theorem succ_inst (A : TF) (a : Term) : (A.subst succσ).inst a = A.inst (succ a) := by
  rw [inst, inst, subst_subst]
  congr 1
  funext k
  cases k <;> rfl

theorem upwk_inst_var (A : TF) : (A.subst (up wk)).inst (var 0) = A := by
  rw [inst, subst_subst]
  have : (fun k => psubst (scons (var 0) var) (up wk k)) = var := by
    funext k; cases k <;> rfl
  rw [this, subst_var]

end TF

/-! ### Conversion of formulas -/

/-- Same shape, with pointwise convertible atoms. -/
def TFConv : TF → TF → Prop
  | .eq a b, .eq a' b' => Conv a a' ∧ Conv b b'
  | .and A B, .and A' B' => TFConv A A' ∧ TFConv B B'
  | .imp A B, .imp A' B' => TFConv A A' ∧ TFConv B B'
  | .ex A, .ex A' => TFConv A A'
  | .all A, .all A' => TFConv A A'
  | _, _ => False

namespace TFConv

theorem eq_iff {a b a' b' : Term} : TFConv (.eq a b) (.eq a' b') ↔ Conv a a' ∧ Conv b b' := by
  simp only [TFConv]
theorem and_iff {A B A' B' : TF} : TFConv (.and A B) (.and A' B') ↔ TFConv A A' ∧ TFConv B B' := by
  simp only [TFConv]
theorem imp_iff {A B A' B' : TF} : TFConv (.imp A B) (.imp A' B') ↔ TFConv A A' ∧ TFConv B B' := by
  simp only [TFConv]
theorem ex_iff {A A' : TF} : TFConv (.ex A) (.ex A') ↔ TFConv A A' := by simp only [TFConv]
theorem all_iff {A A' : TF} : TFConv (.all A) (.all A') ↔ TFConv A A' := by simp only [TFConv]
theorem imp_all {A B C : TF} : ¬ TFConv (.imp A B) (.all C) := by simp only [TFConv]; exact fun h => h
theorem all_imp {A B C : TF} : ¬ TFConv (.all C) (.imp A B) := by simp only [TFConv]; exact fun h => h
theorem and_ex {A B C : TF} : ¬ TFConv (.and A B) (.ex C) := by simp only [TFConv]; exact fun h => h
theorem ex_and {A B C : TF} : ¬ TFConv (.ex C) (.and A B) := by simp only [TFConv]; exact fun h => h

theorem refl : ∀ A : TF, TFConv A A
  | .eq a b => eq_iff.mpr ⟨.refl a, .refl b⟩
  | .and A B => and_iff.mpr ⟨refl A, refl B⟩
  | .imp A B => imp_iff.mpr ⟨refl A, refl B⟩
  | .ex A => ex_iff.mpr (refl A)
  | .all A => all_iff.mpr (refl A)

theorem symm : ∀ {A B : TF}, TFConv A B → TFConv B A
  | .eq _ _, .eq _ _, h => eq_iff.mpr ⟨(eq_iff.mp h).1.symm, (eq_iff.mp h).2.symm⟩
  | .and _ _, .and _ _, h => and_iff.mpr ⟨symm (and_iff.mp h).1, symm (and_iff.mp h).2⟩
  | .imp _ _, .imp _ _, h => imp_iff.mpr ⟨symm (imp_iff.mp h).1, symm (imp_iff.mp h).2⟩
  | .ex _, .ex _, h => ex_iff.mpr (symm (ex_iff.mp h))
  | .all _, .all _, h => all_iff.mpr (symm (all_iff.mp h))
  | .eq _ _, .and _ _, h | .eq _ _, .imp _ _, h | .eq _ _, .ex _, h | .eq _ _, .all _, h
  | .and _ _, .eq _ _, h | .and _ _, .imp _ _, h | .and _ _, .ex _, h | .and _ _, .all _, h
  | .imp _ _, .eq _ _, h | .imp _ _, .and _ _, h | .imp _ _, .ex _, h | .imp _ _, .all _, h
  | .ex _, .eq _ _, h | .ex _, .and _ _, h | .ex _, .imp _ _, h | .ex _, .all _, h
  | .all _, .eq _ _, h | .all _, .and _ _, h | .all _, .imp _ _, h | .all _, .ex _, h =>
    by simp only [TFConv] at h

theorem trans : ∀ {A B C : TF}, TFConv A B → TFConv B C → TFConv A C := by
  intro A
  induction A with
  | eq a b =>
    intro B C h₁ h₂
    cases B <;> cases C <;> simp only [TFConv] at h₁ h₂ ⊢
    exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  | and A B ihA ihB =>
    intro B' C h₁ h₂
    cases B' <;> cases C <;> simp only [TFConv] at h₁ h₂ ⊢
    exact ⟨ihA h₁.1 h₂.1, ihB h₁.2 h₂.2⟩
  | imp A B ihA ihB =>
    intro B' C h₁ h₂
    cases B' <;> cases C <;> simp only [TFConv] at h₁ h₂ ⊢
    exact ⟨ihA h₁.1 h₂.1, ihB h₁.2 h₂.2⟩
  | ex A ih =>
    intro B C h₁ h₂
    cases B <;> cases C <;> simp only [TFConv] at h₁ h₂ ⊢
    exact ih h₁ h₂
  | all A ih =>
    intro B C h₁ h₂
    cases B <;> cases C <;> simp only [TFConv] at h₁ h₂ ⊢
    exact ih h₁ h₂

theorem ty_eq : ∀ {A B : TF}, TFConv A B → A.ty = B.ty := by
  intro A
  induction A with
  | eq => intro B h; cases B <;> simp only [TFConv] at h; rfl
  | and A B ihA ihB =>
    intro C h; cases C <;> simp only [TFConv] at h
    simp only [TF.ty, ihA h.1, ihB h.2]
  | imp A B ihA ihB =>
    intro C h; cases C <;> simp only [TFConv] at h
    simp only [TF.ty, ihA h.1, ihB h.2]
  | ex A ih => intro C h; cases C <;> simp only [TFConv] at h; simp only [TF.ty, ih h]
  | all A ih => intro C h; cases C <;> simp only [TFConv] at h; simp only [TF.ty, ih h]

theorem subst : ∀ {A B : TF}, TFConv A B → ∀ σ, TFConv (A.subst σ) (B.subst σ) := by
  intro A
  induction A with
  | eq a b =>
    intro B h σ; cases B <;> simp only [TFConv, TF.subst] at h ⊢
    exact ⟨h.1.psubst σ, h.2.psubst σ⟩
  | and A B ihA ihB =>
    intro C h σ; cases C <;> simp only [TFConv, TF.subst] at h ⊢
    exact ⟨ihA h.1 σ, ihB h.2 σ⟩
  | imp A B ihA ihB =>
    intro C h σ; cases C <;> simp only [TFConv, TF.subst] at h ⊢
    exact ⟨ihA h.1 σ, ihB h.2 σ⟩
  | ex A ih => intro C h σ; cases C <;> simp only [TFConv, TF.subst] at h ⊢; exact ih h _
  | all A ih => intro C h σ; cases C <;> simp only [TFConv, TF.subst] at h ⊢; exact ih h _

theorem env : ∀ (A : TF) (σ σ' : Nat → Term), (∀ k, σ k ⟶* σ' k) →
    TFConv (A.subst σ) (A.subst σ') := by
  have hup : ∀ σ σ' : Nat → Term, (∀ k, σ k ⟶* σ' k) → ∀ k, up σ k ⟶* up σ' k := by
    intro σ σ' h k
    cases k with
    | zero => exact .refl
    | succ k => simpa only [up_succ, sh_eq] using (h k).psubst wk
  intro A
  induction A with
  | eq a b =>
    intro σ σ' h; simp only [TFConv, TF.subst]
    exact ⟨.of_red (psubst_redStar_env a σ σ' h), .of_red (psubst_redStar_env b σ σ' h)⟩
  | and A B ihA ihB => intro σ σ' h; simp only [TFConv, TF.subst]; exact ⟨ihA σ σ' h, ihB σ σ' h⟩
  | imp A B ihA ihB => intro σ σ' h; simp only [TFConv, TF.subst]; exact ⟨ihA σ σ' h, ihB σ σ' h⟩
  | ex A ih => intro σ σ' h; simp only [TFConv, TF.subst]; exact ih _ _ (hup σ σ' h)
  | all A ih => intro σ σ' h; simp only [TFConv, TF.subst]; exact ih _ _ (hup σ σ' h)

theorem inst_conv (A : TF) {a a' : Term} (h : Conv a a') : TFConv (A.inst a) (A.inst a') := by
  obtain ⟨w, h₁, h₂⟩ := h
  have e : ∀ {x : Term}, x ⟶* w → ∀ k, scons x var k ⟶* scons w var k := by
    intro x hx k; cases k
    · exact hx
    · exact .refl
  exact (env A _ _ (e h₁)).trans (env A _ _ (e h₂)).symm

end TFConv

/-! ## Contexts -/

/-- A context entry: an object variable of type `nat`, or a hypothesis. -/
inductive Entry where
  | obj : Entry
  | prf : TF → Entry

namespace Entry

def subst (σ : Nat → Term) : Entry → Entry
  | .obj => .obj
  | .prf A => .prf (A.subst σ)

def ty : Entry → Ty
  | .obj => nat
  | .prf A => A.ty

@[simp] theorem ty_subst (e : Entry) (σ : Nat → Term) : (e.subst σ).ty = e.ty := by
  cases e <;> simp [subst, ty]

theorem wk_up (e : Entry) (σ : Nat → Term) : (e.subst wk).subst (up σ) = (e.subst σ).subst wk := by
  cases e <;> simp [subst, TF.wk_up]

end Entry

/-- Contexts are infinite; each entry is relative to the whole context. -/
abbrev Ctx := Nat → Entry

/-- Push an entry (relative to `D`) onto `D`, shifting everything. -/
def ext (e : Entry) (D : Ctx) : Ctx := scons (e.subst wk) (fun k => (D k).subst wk)

def erase (D : Ctx) : Nat → Ty := fun k => (D k).ty

theorem erase_ext (e : Entry) (D : Ctx) : erase (ext e D) = scons e.ty (erase D) := by
  funext k; cases k <;> simp [erase, ext]

/-! ## The judgment -/

/-- The dummy step function of an equality elimination. -/
def K' : Term := lam (lam (var 0))

set_option hygiene false in
/-- `D ⊢ t ⊩ A` (that is, `RJ D t A`): the T-term `t` realizes the formula `A`
in context `D`. -/
notation:50 D:51 " ⊢ " t:51 " ⊩ " A:51 => RJ D t A

/-- The realizability judgment `D ⊢ t ⊩ A`. -/
inductive RJ : Ctx → Term → TF → Prop where
| var : D k = .prf A → D ⊢ var k ⊩ A
| lamI : ext (.prf A) D ⊢ t ⊩ TF.subst wk B → D ⊢ lam t ⊩ .imp A B
| appI : D ⊢ t ⊩ .imp A B → D ⊢ u ⊩ A → D ⊢ app t u ⊩ B
| lamA : ext .obj D ⊢ t ⊩ B → D ⊢ lam t ⊩ .all B
| appA : D ⊢ t ⊩ .all B → HasTypeF (erase D) a nat → D ⊢ app t a ⊩ TF.inst B a
| pairC : D ⊢ a ⊩ A → D ⊢ b ⊩ B → D ⊢ pair a b ⊩ .and A B
| fstC : D ⊢ t ⊩ .and A B → D ⊢ fst t ⊩ A
| sndC : D ⊢ t ⊩ .and A B → D ⊢ snd t ⊩ B
| pairE : HasTypeF (erase D) w nat → D ⊢ b ⊩ TF.inst B w → D ⊢ pair w b ⊩ .ex B
| sndE : D ⊢ p ⊩ .ex B → D ⊢ snd p ⊩ TF.inst B (fst p)
| refl : Conv a b → D ⊢ zero ⊩ .eq a b
| eqElim : D ⊢ e ⊩ .eq a b → D ⊢ t ⊩ TF.inst A a → D ⊢ rect t K' e ⊩ TF.inst A b
| botE : D ⊢ e ⊩ .eq zero (succ c) → D ⊢ rect (dflt (TF.ty A)) K' e ⊩ A
| ind : D ⊢ z ⊩ TF.inst A zero → D ⊢ s ⊩ .all (.imp A (TF.subst TF.succσ A)) →
    HasTypeF (erase D) n nat → D ⊢ rect z s n ⊩ TF.inst A n
| conv : D ⊢ t ⊩ A → TFConv A B → D ⊢ t ⊩ B

/-- Realizers are well-typed System T terms. -/
theorem RJ.erase {D : Ctx} {t : Term} {A : TF} (h : D ⊢ t ⊩ A) : HasTypeF (erase D) t A.ty := by
  induction h with
  | var hk => exact .var' (by simp only [Rz.erase, hk, Entry.ty])
  | lamI _ ih =>
    rw [erase_ext, TF.ty_subst] at ih
    exact .lam ih
  | appI _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lamA _ ih => rw [erase_ext] at ih; exact .lam ih
  | appA _ ha ih => rw [TF.inst, TF.ty_subst]; exact .app ih ha
  | pairC _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | fstC _ ih => exact .fst ih
  | sndC _ ih => exact .snd ih
  | pairE hw _ ih => rw [TF.inst, TF.ty_subst] at ih; exact .pair hw ih
  | sndE _ ih => rw [TF.inst, TF.ty_subst]; exact .snd ih
  | refl _ => exact .zero
  | eqElim _ _ ihe iht =>
    rw [TF.inst, TF.ty_subst] at iht ⊢
    exact .rect iht (.lam (.lam .var)) ihe
  | botE _ ihe => exact .rect ((dflt_typed _).toF _) (.lam (.lam .var)) ihe
  | ind _ _ hn ihz ihs =>
    rw [TF.inst, TF.ty_subst] at ihz ⊢
    simp only [TF.ty, TF.ty_subst] at ihs
    exact .rect ihz ihs hn
  | conv _ hc ih => rw [← TFConv.ty_eq hc]; exact ih

/-! ## Substitution -/

structure SubstOK (D D' : Ctx) (σ : Nat → Term) : Prop where
  ty : ∀ k, HasTypeF (erase D') (σ k) (erase D k)
  prf : ∀ k A, D k = .prf A → D' ⊢ σ k ⊩ A.subst σ

theorem RJ.botE' {D : Ctx} {e c : Term} (h : D ⊢ e ⊩ .eq zero (succ c)) (A : TF)
    (σ : Nat → Term) : D ⊢ rect (dflt A.ty) K' e ⊩ A.subst σ := by
  have := RJ.botE (A := A.subst σ) h
  rwa [TF.ty_subst] at this

/-- Substitution for any class of substitutions closed under lifting. -/
theorem RJ.subst_gen (P : Ctx → Ctx → (Nat → Term) → Prop)
    (hok : ∀ {D D' σ}, P D D' σ → SubstOK D D' σ)
    (hup : ∀ {D D' σ} (e : Entry), P D D' σ → P (ext e D) (ext (e.subst σ) D') (up σ))
    {D : Ctx} {t : Term} {A : TF} (h : D ⊢ t ⊩ A) :
    ∀ {D' σ}, P D D' σ → D' ⊢ psubst σ t ⊩ A.subst σ := by
  induction h with
  | var hk => intro D' σ hP; exact (hok hP).prf _ _ hk
  | lamI _ ih =>
    intro D' σ hP
    have := ih (hup _ hP)
    rw [TF.wk_up] at this
    exact .lamI this
  | appI _ _ ih₁ ih₂ => intro D' σ hP; exact .appI (ih₁ hP) (ih₂ hP)
  | lamA _ ih => intro D' σ hP; exact .lamA (ih (hup .obj hP))
  | appA _ ha ih =>
    intro D' σ hP
    rw [TF.inst_subst]
    exact .appA (ih hP) (ha.psubst _ _ (hok hP).ty)
  | pairC _ _ ih₁ ih₂ => intro D' σ hP; exact .pairC (ih₁ hP) (ih₂ hP)
  | fstC _ ih => intro D' σ hP; exact .fstC (ih hP)
  | sndC _ ih => intro D' σ hP; exact .sndC (ih hP)
  | pairE hw _ ih =>
    intro D' σ hP
    have := ih hP
    rw [TF.inst_subst] at this
    exact .pairE (hw.psubst _ _ (hok hP).ty) this
  | sndE _ ih => intro D' σ hP; rw [TF.inst_subst]; exact .sndE (ih hP)
  | refl hc => intro D' σ hP; exact .refl (hc.psubst σ)
  | eqElim _ _ ihe iht =>
    intro D' σ hP
    have ht := iht hP
    rw [TF.inst_subst] at ht
    rw [TF.inst_subst]
    exact .eqElim (ihe hP) ht
  | botE _ ih =>
    intro D' σ hP
    simp only [psubst, psubst_dflt]
    exact RJ.botE' (ih hP) _ σ
  | ind _ _ hn ihz ihs =>
    intro D' σ hP
    have hz := ihz hP
    rw [TF.inst_subst] at hz
    have hs := ihs hP
    simp only [TF.subst] at hs
    rw [TF.succ_up] at hs
    rw [TF.inst_subst]
    exact .ind hz hs (hn.psubst _ _ (hok hP).ty)
  | conv _ hc ih => intro D' σ hP; exact .conv (ih hP) (hc.subst σ)

/-- Renamings. -/
def IsRen (D D' : Ctx) (σ : Nat → Term) : Prop :=
  ∃ ξ : Nat → Nat, σ = (fun k => var (ξ k)) ∧ ∀ k, D' (ξ k) = (D k).subst σ

theorem IsRen.ok {D D' : Ctx} {σ : Nat → Term} (h : IsRen D D' σ) : SubstOK D D' σ := by
  obtain ⟨ξ, rfl, hξ⟩ := h
  refine ⟨fun k => .var' ?_, fun k A hk => .var ?_⟩
  · simp only [Rz.erase, hξ k, Entry.ty_subst]
  · rw [hξ k, hk]; rfl

theorem IsRen.up {D D' : Ctx} {σ : Nat → Term} (e : Entry) (h : IsRen D D' σ) :
    IsRen (ext e D) (ext (e.subst σ) D') (Rz.up σ) := by
  obtain ⟨ξ, rfl, hξ⟩ := h
  refine ⟨scons 0 (fun k => ξ k + 1), ?_, ?_⟩
  · funext k; cases k <;> rfl
  · intro k
    cases k with
    | zero => exact (Entry.wk_up e _).symm
    | succ k =>
      show (D' (ξ k)).subst wk = ((D k).subst wk).subst _
      rw [hξ k, Entry.wk_up]

theorem RJ.weaken {D : Ctx} {t : Term} {A : TF} (h : D ⊢ t ⊩ A) (e : Entry) :
    ext e D ⊢ psubst wk t ⊩ A.subst wk :=
  RJ.subst_gen IsRen (fun h => h.ok) (fun e h => h.up e) h ⟨(· + 1), rfl, fun _ => rfl⟩

theorem SubstOK.wk {D : Ctx} (e : Entry) : SubstOK D (ext e D) Rz.wk :=
  IsRen.ok ⟨(· + 1), rfl, fun _ => rfl⟩

theorem SubstOK.up {D D' : Ctx} {σ : Nat → Term} (h : SubstOK D D' σ) (e : Entry) :
    SubstOK (ext e D) (ext (e.subst σ) D') (Rz.up σ) where
  ty k := by
    rw [erase_ext, erase_ext]
    cases k with
    | zero => exact .var' (by simp)
    | succ k => exact (h.ty k).sh
  prf k A hk := by
    cases k with
    | zero =>
      cases e with
      | obj => simp [ext, Entry.subst] at hk
      | prf B =>
        simp only [ext, scons_zero, Entry.subst, Entry.prf.injEq] at hk
        subst hk
        rw [TF.wk_up]
        exact .var rfl
    | succ k =>
      cases hD : D k with
      | obj => simp [ext, hD, Entry.subst] at hk
      | prf B =>
        simp only [ext, scons_succ, hD, Entry.subst, Entry.prf.injEq] at hk
        subst hk
        rw [TF.wk_up, up_succ, sh_eq]
        exact (h.prf k B hD).weaken _

theorem RJ.subst {D D' : Ctx} {σ : Nat → Term} {t : Term} {A : TF} (h : D ⊢ t ⊩ A)
    (hσ : SubstOK D D' σ) : D' ⊢ psubst σ t ⊩ A.subst σ :=
  RJ.subst_gen SubstOK (fun h => h) (fun e h => h.up e) h hσ

theorem SubstOK.id (D : Ctx) : SubstOK D D var :=
  ⟨fun _ => .var, fun _ A hk => by rw [TF.subst_var]; exact .var hk⟩

theorem SubstOK.comp {D D' D'' : Ctx} {σ τ : Nat → Term} (h₁ : SubstOK D D' σ)
    (h₂ : SubstOK D' D'' τ) : SubstOK D D'' (fun k => psubst τ (σ k)) :=
  ⟨fun k => (h₁.ty k).psubst _ _ h₂.ty,
   fun k A hk => by rw [← TF.subst_subst]; exact (h₁.prf k A hk).subst h₂⟩

theorem SubstOK.cons {D D' : Ctx} {σ : Nat → Term} {u : Term} {B : TF} (h : SubstOK D D' σ)
    (hu : D' ⊢ u ⊩ B.subst σ) : SubstOK (ext (.prf B) D) D' (scons u σ) where
  ty k := by
    rw [erase_ext]
    cases k with
    | zero => have := hu.erase; rw [TF.ty_subst] at this; exact this
    | succ k => exact h.ty k
  prf k A hk := by
    cases k with
    | zero =>
      simp only [ext, scons_zero, Entry.subst, Entry.prf.injEq] at hk
      subst hk
      rw [TF.subst_wk_scons]
      exact hu
    | succ k =>
      cases hD : D k with
      | obj => simp [ext, hD, Entry.subst] at hk
      | prf C =>
        simp only [ext, scons_succ, hD, Entry.subst, Entry.prf.injEq] at hk
        subst hk
        rw [TF.subst_wk_scons]
        exact h.prf k C hD

theorem SubstOK.consObj {D D' : Ctx} {σ : Nat → Term} {a : Term} (h : SubstOK D D' σ)
    (ha : HasTypeF (erase D') a nat) : SubstOK (ext .obj D) D' (scons a σ) where
  ty k := by
    rw [erase_ext]
    cases k with
    | zero => exact ha
    | succ k => exact h.ty k
  prf k A hk := by
    cases k with
    | zero => simp [ext, Entry.subst] at hk
    | succ k =>
      cases hD : D k with
      | obj => simp [ext, hD, Entry.subst] at hk
      | prf C =>
        simp only [ext, scons_succ, hD, Entry.subst, Entry.prf.injEq] at hk
        subst hk
        rw [TF.subst_wk_scons]
        exact h.prf k C hD

/-! ## Inversion -/

theorem RJ.lam_inv {D : Ctx} {t : Term} {X : TF} (h : D ⊢ lam t ⊩ X) :
    (∃ A B, TFConv (.imp A B) X ∧ ext (.prf A) D ⊢ t ⊩ B.subst wk) ∨
    (∃ B, TFConv (.all B) X ∧ ext .obj D ⊢ t ⊩ B) := by
  generalize e : Term.lam t = s at h
  induction h with
  | lamI h => cases e; exact .inl ⟨_, _, TFConv.refl _, h⟩
  | lamA h => cases e; exact .inr ⟨_, TFConv.refl _, h⟩
  | conv _ hc ih =>
    rcases ih e with ⟨A, B, h₁, h₂⟩ | ⟨B, h₁, h₂⟩
    · exact .inl ⟨A, B, h₁.trans hc, h₂⟩
    · exact .inr ⟨B, h₁.trans hc, h₂⟩
  | _ => cases e

theorem RJ.pair_inv {D : Ctx} {a b : Term} {X : TF} (h : D ⊢ pair a b ⊩ X) :
    (∃ A B, TFConv (.and A B) X ∧ D ⊢ a ⊩ A ∧ D ⊢ b ⊩ B) ∨
    (∃ B, TFConv (.ex B) X ∧ HasTypeF (Rz.erase D) a nat ∧ D ⊢ b ⊩ B.inst a) := by
  generalize e : Term.pair a b = s at h
  induction h with
  | pairC ha hb => cases e; exact .inl ⟨_, _, TFConv.refl _, ha, hb⟩
  | pairE hw hb => cases e; exact .inr ⟨_, TFConv.refl _, hw, hb⟩
  | conv _ hc ih =>
    rcases ih e with ⟨A, B, h₁, h₂, h₃⟩ | ⟨B, h₁, h₂, h₃⟩
    · exact .inl ⟨A, B, h₁.trans hc, h₂, h₃⟩
    · exact .inr ⟨B, h₁.trans hc, h₂, h₃⟩
  | _ => cases e

theorem RJ.zero_inv {D : Ctx} {X : TF} (h : D ⊢ zero ⊩ X) :
    ∃ a b, Conv a b ∧ TFConv (.eq a b) X := by
  generalize e : Term.zero = s at h
  induction h with
  | refl hc => exact ⟨_, _, hc, TFConv.refl _⟩
  | conv _ hc ih =>
    obtain ⟨a, b, h₁, h₂⟩ := ih e
    exact ⟨a, b, h₁, h₂.trans hc⟩
  | _ => cases e

theorem RJ.succ_inv {D : Ctx} {n : Term} {X : TF} (h : D ⊢ succ n ⊩ X) : False := by
  generalize e : Term.succ n = s at h
  induction h with
  | conv _ _ ih => exact ih e
  | _ => cases e

/-- A numeral realizing an equation witnesses its truth (up to conversion). -/
theorem RJ.numeral_inv {D : Ctx} {n : Nat} {a b : Term} (h : D ⊢ numeral n ⊩ .eq a b) :
    Conv a b := by
  cases n with
  | zero =>
    obtain ⟨a', b', hab, hc⟩ := RJ.zero_inv h
    obtain ⟨h₁, h₂⟩ := TFConv.eq_iff.mp hc
    exact (h₁.symm.trans hab).trans h₂
  | succ n => exact (RJ.succ_inv h).elim

/-- **No numeral realizes `⊥`.** -/
theorem no_numeral_bot {D : Ctx} {n : Nat} : ¬ D ⊢ numeral n ⊩ TF.bot :=
  fun h => not_conv_zero_succ (RJ.numeral_inv h)

/-! ## Subject reduction -/

theorem K'_normal {s : Term} : ¬ Red K' s := by
  intro r
  cases r with
  | lam r => cases r with
    | lam r => cases r

theorem dflt_normal : ∀ (A : Ty) {s : Term}, ¬ Red (dflt A) s
  | .nat, _, r => by cases r
  | .arrow _ B, _, r => by
    cases r with
    | lam r => exact dflt_normal B r
  | .prod A B, _, r => by
    cases r with
    | pairL r => exact dflt_normal A r
    | pairR r => exact dflt_normal B r

theorem RJ.red {D : Ctx} {t : Term} {A : TF} (h : D ⊢ t ⊩ A) : ∀ {t'}, Red t t' → D ⊢ t' ⊩ A := by
  induction h with
  | var _ => intro t' r; cases r
  | lamI _ ih => intro t' r; cases r with | lam r => exact .lamI (ih r)
  | lamA _ ih => intro t' r; cases r with | lam r => exact .lamA (ih r)
  | appI ht hu iht ihu =>
    intro t' r
    cases r with
    | beta =>
      rcases ht.lam_inv with ⟨A', B', hc, hb⟩ | ⟨B', hc, _⟩
      · obtain ⟨hcA, hcB⟩ := TFConv.imp_iff.mp hc
        rw [subst_single]
        have := hb.subst ((SubstOK.id _).cons (B := A')
          (by rw [TF.subst_var]; exact hu.conv hcA.symm))
        rw [TF.subst_wk_scons, TF.subst_var] at this
        exact this.conv hcB
      · exact (TFConv.all_imp hc).elim
    | appL r => exact .appI (iht r) hu
    | appR r => exact .appI ht (ihu r)
  | appA ht ha iht =>
    intro t' r
    cases r with
    | beta =>
      rcases ht.lam_inv with ⟨_, _, hc, _⟩ | ⟨B', hc, hb⟩
      · exact (TFConv.imp_all hc).elim
      · rw [subst_single]
        have := hb.subst ((SubstOK.id _).consObj ha)
        exact this.conv (TFConv.subst (TFConv.all_iff.mp hc) _)
    | appL r => exact .appA (iht r) ha
    | appR r =>
      exact .conv (.appA ht (ha.red r)) (TFConv.inst_conv _ (Conv.of_red (.single r)).symm)
  | pairC _ _ iha ihb =>
    intro t' r
    cases r with
    | pairL r => exact .pairC (iha r) ‹_›
    | pairR r => exact .pairC ‹_› (ihb r)
  | fstC ht iht =>
    intro t' r
    cases r with
    | fstβ =>
      rcases ht.pair_inv with ⟨_, _, hc, ha, _⟩ | ⟨_, hc, _, _⟩
      · exact ha.conv (TFConv.and_iff.mp hc).1.symm.symm
      · exact (TFConv.ex_and hc).elim
    | fst r => exact .fstC (iht r)
  | sndC ht iht =>
    intro t' r
    cases r with
    | sndβ =>
      rcases ht.pair_inv with ⟨_, _, hc, _, hb⟩ | ⟨_, hc, _, _⟩
      · exact hb.conv (TFConv.and_iff.mp hc).2
      · exact (TFConv.ex_and hc).elim
    | snd r => exact .sndC (iht r)
  | pairE hw hb ihb =>
    intro t' r
    cases r with
    | pairL r => exact .pairE (hw.red r) (hb.conv (TFConv.inst_conv _ (Conv.of_red (.single r))))
    | pairR r => exact .pairE hw (ihb r)
  | sndE hp ihp =>
    intro t' r
    cases r with
    | sndβ =>
      rcases hp.pair_inv with ⟨_, _, hc, _, _⟩ | ⟨B', hc, _, hb⟩
      · exact (TFConv.and_ex hc).elim
      · exact hb.conv ((TFConv.subst (TFConv.ex_iff.mp hc) _).trans
          (TFConv.inst_conv _ (Conv.of_red (.single .fstβ)).symm))
    | snd r =>
      exact .conv (.sndE (ihp r)) (TFConv.inst_conv _ (Conv.of_red (.single (.fst r))).symm)
  | refl _ => intro t' r; cases r
  | eqElim he ht ihe iht =>
    intro t' r
    cases r with
    | rectz =>
      obtain ⟨a', b', hab, hc⟩ := he.zero_inv
      obtain ⟨h₁, h₂⟩ := TFConv.eq_iff.mp hc
      exact ht.conv (TFConv.inst_conv _ ((h₁.symm.trans hab).trans h₂))
    | rects => exact he.succ_inv.elim
    | rectZ r => exact .eqElim he (iht r)
    | rectS r => exact (K'_normal r).elim
    | rectT r => exact .eqElim (ihe r) ht
  | botE he ihe =>
    intro t' r
    cases r with
    | rectz =>
      obtain ⟨a', b', hab, hc⟩ := he.zero_inv
      obtain ⟨h₁, h₂⟩ := TFConv.eq_iff.mp hc
      exact (not_conv_zero_succ ((h₁.symm.trans hab).trans h₂)).elim
    | rects => exact he.succ_inv.elim
    | rectZ r => exact (dflt_normal _ r).elim
    | rectS r => exact (K'_normal r).elim
    | rectT r => exact .botE (ihe r)
  | ind hz hs hn ihz ihs =>
    intro t' r
    cases r with
    | rectz => exact hz
    | rects =>
      cases hn with
      | succ hm =>
        have h₂ : _ ⊢ app (app _ _) (rect _ _ _) ⊩ (TF.subst TF.succσ _).inst _ :=
          RJ.appI (RJ.appA hs hm) (RJ.ind hz hs hm)
        rwa [TF.succ_inst] at h₂
    | rectZ r => exact .ind (ihz r) hs hn
    | rectS r => exact .ind hz (ihs r) hn
    | rectT r =>
      exact .conv (.ind hz hs (hn.red r)) (TFConv.inst_conv _ (Conv.of_red (.single r)).symm)
  | conv _ hc ih => intro t' r; exact .conv (ih r) hc

theorem RJ.redStar {D : Ctx} {t t' : Term} {A : TF} (h : D ⊢ t ⊩ A) (r : t ⟶* t') : D ⊢ t' ⊩ A := by
  induction r with
  | refl => exact h
  | step r _ ih => exact ih (h.red r)

end Rz
