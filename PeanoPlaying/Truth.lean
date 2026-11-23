import PeanoPlaying.JSoundness
import PeanoPlaying.Arith

/-!
# Truth and realizability

Two bridges between `sat` (truth in the standard model) and the
realizability judgment, for formulas whose free variables are read as
numerals (`numEnv e`):

* `Sig.realize`: a **true Σ-formula** (built from `=`, `⊥`, `∧`, `∨`, `∃` and
  bounded `∀ x < y`) has a realizer, in every context. This is the content of
  Σ₁-completeness. Bounded universals are realized by a case analysis on
  the bound, carried out inside the judgment (`RJ.ball`).
* `Pos.sound`: a **realized positive formula** (built from `=`, `⊥`, `∧`, `∨`,
  `∃`, `∀` and `σ ⊃ ψ` with `σ` a Σ-formula) is true. This uses
  normalization (a `NatNorm` hypothesis): closed realizers of `∃` are
  evaluated to get the witness.
  It generalizes `forall_exists_eq` from equations to arbitrary positive
  formulas, bounded quantifiers included.
-/

namespace Rz

open Term Ty

/-! ## Environments of numerals -/

theorem sh_numeral (n : Nat) : sh (numeral n) = numeral n := by
  rw [sh_eq, psubst_numeral]

theorem up_numEnv (e : Nat → Nat) : up (numEnv e) = scons (Term.var 0) (numEnv e) := by
  funext k; cases k with
  | zero => rfl
  | succ k => exact sh_numeral _

theorem scons_numEnv (n : Nat) (e : Nat → Nat) :
    scons (numeral n) (numEnv e) = numEnv (scons n e) := by
  funext k; cases k <;> rfl

/-- Formula families `a ↦ ⟦φ⟧(a, e)`, with all other variables numerals. -/
def Fam (φ : HA.Formula) (e : Nat → Nat) (a : Term) : TF := toTF (scons a (numEnv e)) φ

theorem Fam_subst (φ : HA.Formula) (e : Nat → Nat) (a : Term) (σ : Nat → Term) :
    (Fam φ e a).subst σ = Fam φ e (psubst σ a) := by
  rw [Fam, toTF_subst, Fam]
  congr 1; funext k; cases k with
  | zero => rfl
  | succ k => exact psubst_numeral _ _

theorem Fam_inst (φ : HA.Formula) (e : Nat → Nat) (a b : Term) :
    (Fam φ e a).inst b = Fam φ e (psubst (scons b Term.var) a) := Fam_subst _ _ _ _

theorem Fam_numeral (φ : HA.Formula) (e : Nat → Nat) (n : Nat) :
    Fam φ e (numeral n) = toTF (numEnv (scons n e)) φ := by
  rw [Fam, scons_numEnv]

theorem toTF_up_numEnv (φ : HA.Formula) (e : Nat → Nat) :
    toTF (up (numEnv e)) φ = Fam φ e (Term.var 0) := by
  rw [Fam, up_numEnv]

theorem toTF_numEnv_subst (φ : HA.Formula) (e : Nat → Nat) (σ : Nat → Term) :
    (toTF (numEnv e) φ).subst σ = toTF (numEnv e) φ := by
  rw [toTF_subst]
  congr 1; funext k; exact psubst_numeral _ _

theorem toTF_ex_inst (φ : HA.Formula) (e : Nat → Nat) (n : Nat) :
    (toTF (up (numEnv e)) φ).inst (numeral n) = toTF (numEnv (scons n e)) φ := by
  rw [toTF_up_numEnv, Fam_inst]; exact Fam_numeral _ _ _

theorem tr_numEnv_conv (e : Nat → Nat) (a : HA.Tm) : Conv (tr (numEnv e) a) (numeral (eval e a)) :=
  Conv.of_red (tr_eval e a)

/-! ## Derived equality rules -/

theorem RJ.eqSymm {D : Ctx} {p a b : Term} (h : D ⊢ p ⊩ .eq a b) : ∃ q, D ⊢ q ⊩ .eq b a := by
  have hM : ∀ x, (TF.eq (Term.var 0) (psubst wk a)).inst x = .eq x a := by
    intro x
    simp only [TF.inst, TF.subst, psubst, scons_zero, psubst_wk_scons, psubst_var]
  have h0 : D ⊢ zero ⊩ (TF.eq (Term.var 0) (psubst wk a)).inst a := by
    rw [hM]; exact .refl (Conv.refl _)
  have := RJ.eqElim h h0
  rw [hM] at this
  exact ⟨_, this⟩

/-- Transport along a realized equation, in a family. -/
theorem RJ.transport {D : Ctx} {p a b r : Term} (φ : HA.Formula) (e : Nat → Nat)
    (hp : D ⊢ p ⊩ .eq a b) (hr : D ⊢ r ⊩ Fam φ e a) : ∃ r', D ⊢ r' ⊩ Fam φ e b := by
  have hi : ∀ x, (Fam φ e (Term.var 0)).inst x = Fam φ e x := fun x => by
    rw [Fam_inst]; rfl
  have := RJ.eqElim (A := Fam φ e (Term.var 0)) hp (by rw [hi]; exact hr)
  rw [hi] at this
  exact ⟨_, this⟩

/-! ## Realizing bounded universals -/

/-- `x < L`, as the translation of `∃k. x + S k = L`. -/
def LtF (x : Term) (L : Nat) : TF :=
  .ex (.eq (rect (sh x) addStep (succ (Term.var 0))) (numeral L))

theorem LtF_inst (x k : Term) (L : Nat) :
    (TF.eq (rect (sh x) addStep (succ (Term.var 0))) (numeral L)).inst k =
      .eq (rect x addStep (succ k)) (numeral L) := by
  simp only [TF.inst, TF.subst, psubst, psubst_sh_scons, psubst_var, psubst_numeral, scons_zero,
    psubst_addStep]

theorem HasTypeF.sh_ext {D : Ctx} {x : Term} (en : Entry) (h : HasTypeF (Rz.erase D) x nat) :
    HasTypeF (Rz.erase (ext en D)) (Rz.sh x) nat := by
  rw [erase_ext]; exact h.sh

/-- Case analysis on a bound `L`: from realizers of every instance below `L`,
realize the instance at any `x` with a realizer of `x < L`. -/
theorem RJ.ballCase (φ : HA.Formula) (e : Nat → Nat) : ∀ (L : Nat),
    (∀ n < L, ∀ D, ∃ r, D ⊢ r ⊩ Fam φ e (numeral n)) →
    ∀ (D : Ctx) (x h : Term), HasTypeF (Rz.erase D) x nat → D ⊢ h ⊩ LtF x L →
      ∃ r, D ⊢ r ⊩ Fam φ e x := by
  intro L
  induction L with
  | zero =>
    intro _ D x h _ hh
    have h1 := RJ.sndE hh
    rw [LtF_inst] at h1
    have h2 := h1.conv (TFConv.eq_iff.mpr ⟨Conv.of_red (red_add_succ _ _), Conv.refl _⟩)
    obtain ⟨q, hq⟩ := RJ.eqSymm h2
    exact ⟨_, RJ.botE (c := rect x addStep (fst h)) hq⟩
  | succ L ih =>
    intro hyp D x h hx hh
    -- the motive, with `k` as variable `0`
    let A : TF := .imp (.eq (rect (sh x) addStep (succ (Term.var 0))) (numeral (L + 1)))
      (Fam φ e (sh x))
    have hA0 : A.inst zero = .imp (.eq (rect x addStep (succ zero)) (numeral (L + 1)))
        (Fam φ e x) := by
      simp only [A, TF.inst, TF.subst, psubst, psubst_sh_scons, psubst_var, psubst_numeral,
        scons_zero, psubst_addStep]
      rw [← TF.inst, Fam_inst, psubst_sh_scons, psubst_var]
    have hAk : ∀ k, A.inst k = .imp (.eq (rect x addStep (succ k)) (numeral (L + 1)))
        (Fam φ e x) := by
      intro k
      simp only [A, TF.inst, TF.subst, psubst, psubst_sh_scons, psubst_var, psubst_numeral,
        scons_zero, psubst_addStep]
      rw [← TF.inst, Fam_inst, psubst_sh_scons, psubst_var]
    -- base case: `k = 0`, so `x = L`
    have hz : ∃ z, D ⊢ z ⊩ A.inst zero := by
      rw [hA0]
      let D₁ := ext (.prf (.eq (rect x addStep (succ zero)) (numeral (L + 1)))) D
      have hv : D₁ ⊢ Term.var 0 ⊩ .eq (rect (sh x) addStep (succ zero)) (numeral (L + 1)) := by
        refine .var ?_
        simp only [D₁, ext, scons_zero, Entry.subst, TF.subst, psubst, psubst_numeral,
          psubst_addStep, ← sh_eq]
      have hv' := hv.conv (TFConv.eq_iff.mpr
        ⟨Conv.of_red ((red_add_succ _ _).trans (red_add_zero _).succ), Conv.refl _⟩)
      have he := RJ.succInj hv'
      obtain ⟨q, hq⟩ := RJ.eqSymm he
      obtain ⟨r, hr⟩ := hyp L (by omega) D₁
      obtain ⟨r', hr'⟩ := RJ.transport φ e hq hr
      have h' : D₁ ⊢ r' ⊩ (Fam φ e x).subst wk := by rw [Fam_subst, ← sh_eq]; exact hr'
      exact ⟨_, .lamI h'⟩
    -- step case: `k = S k'`, so `x + S k' = L`
    have hs : ∃ s, D ⊢ s ⊩ .all (.imp A (A.subst TF.succσ)) := by
      have hAS : (A.subst TF.succσ).subst wk =
          .imp (.eq (rect (sh (sh x)) addStep (succ (succ (Term.var 1)))) (numeral (L + 1)))
            (Fam φ e (sh (sh x))) := by
        simp only [A, TF.subst, psubst, psubst_numeral, psubst_addStep, TF.succσ, scons_zero,
          Fam_subst, psubst_sh_scons, wk_apply]
        rw [← sh_eq, ← sh_eq]
      let D₂ := ext (.prf A) (ext .obj D)
      let E₂ := TF.eq (rect (sh (sh x)) addStep (succ (succ (Term.var 1)))) (numeral (L + 1))
      let D₃ := ext (.prf E₂) D₂
      have hv : D₃ ⊢ Term.var 0 ⊩
          .eq (rect (sh (sh (sh x))) addStep (succ (succ (Term.var 2)))) (numeral (L + 1)) := by
        refine .var ?_
        simp only [D₃, E₂, ext, scons_zero, Entry.subst, TF.subst, psubst, psubst_numeral,
          psubst_addStep, wk_apply, ← sh_eq]
      have hv' := hv.conv (TFConv.eq_iff.mpr ⟨Conv.of_red (red_add_succ _ _), Conv.refl _⟩)
      have he := RJ.succInj hv'
      have hx3 : HasTypeF (Rz.erase D₃) (sh (sh (sh x))) nat :=
        ((hx.sh_ext _).sh_ext _).sh_ext _
      have hk : HasTypeF (Rz.erase D₃) (Term.var 2) nat := by
        refine .var' ?_
        simp only [D₃, D₂, erase_ext, scons_succ, scons_zero, Entry.ty]
      have hlt : D₃ ⊢ pair (Term.var 2) (rect zero K' (Term.var 0)) ⊩ LtF (sh (sh (sh x))) L := by
        refine .pairE hk ?_
        rw [LtF_inst]; exact he
      obtain ⟨r, hr⟩ := ih (fun n hn => hyp n (by omega)) D₃ _ _ hx3 hlt
      have h' : D₃ ⊢ r ⊩ (Fam φ e (sh (sh x))).subst wk := by rw [Fam_subst, ← sh_eq]; exact hr
      have h'' : D₂ ⊢ lam r ⊩ (A.subst TF.succσ).subst wk := by rw [hAS]; exact .lamI h'
      exact ⟨_, .lamA (.lamI h'')⟩
    obtain ⟨z, hz⟩ := hz
    obtain ⟨s, hs⟩ := hs
    have hfst : HasTypeF (Rz.erase D) (fst h) nat := .fst hh.erase
    have hR := RJ.ind hz hs hfst
    rw [hAk] at hR
    have hS := RJ.sndE hh
    rw [LtF_inst] at hS
    exact ⟨_, .appI hR hS⟩

/-- The bounded universal `∀x. (∃k. x + S k = y) ⊃ φ` with `y` a variable. -/
def ballF (m : Nat) (φ : HA.Formula) : HA.Formula :=
  .all (.imp (.ex (.eq (.add (.var 1) (.succ (.var 0))) (.var (m + 2)))) φ)

theorem sat_ballF (e : Nat → Nat) (m : Nat) (φ : HA.Formula) :
    sat e (ballF m φ) ↔ ∀ n < e m, sat (scons n e) φ := by
  simp only [ballF, sat_all, sat_imp, sat_ex, sat_eq, eval_add, eval_var, eval_succ,
    scons_succ, scons_zero, exists_add_succ]

theorem RJ.ball (φ : HA.Formula) (e : Nat → Nat) (m : Nat)
    (hyp : ∀ n < e m, ∀ D, ∃ r, D ⊢ r ⊩ toTF (numEnv (scons n e)) φ) (D : Ctx) :
    ∃ r, D ⊢ r ⊩ toTF (numEnv e) (ballF m φ) := by
  have hyp' : ∀ n < e m, ∀ D, ∃ r, D ⊢ r ⊩ Fam φ e (numeral n) := by
    intro n hn D; rw [Fam_numeral]; exact hyp n hn D
  let D₁ := ext (.prf (LtF (Term.var 0) (e m))) (ext .obj D)
  have hx : HasTypeF (Rz.erase D₁) (Term.var 1) nat := by
    refine .var' ?_
    simp only [D₁, erase_ext, scons_succ, scons_zero, Entry.ty]
  have hh : D₁ ⊢ Term.var 0 ⊩ LtF (Term.var 1) (e m) := by
    refine .var ?_
    simp only [D₁, ext, scons_zero, Entry.subst, LtF, TF.subst, psubst, psubst_numeral,
      psubst_addStep, up_zero, up_succ, wk_apply, sh_var]
  obtain ⟨r, hr⟩ := RJ.ballCase φ e (e m) hyp' D₁ _ _ hx hh
  refine ⟨lam (lam r), ?_⟩
  -- the translated formula
  have hT : toTF (numEnv e) (ballF m φ) =
      .all (.imp (LtF (Term.var 0) (e m)) (Fam φ e (Term.var 0))) := by
    have hm : up (up (numEnv e)) (m + 2) = numeral (e m) := by
      show sh (sh (numeral (e m))) = _
      rw [sh_numeral, sh_numeral]
    show TF.all (.imp (.ex (.eq (rect (up (up (numEnv e)) 1) addStep (succ (up (up (numEnv e)) 0)))
      (up (up (numEnv e)) (m + 2)))) (toTF (up (numEnv e)) φ)) = _
    rw [hm, toTF_up_numEnv]
    rfl
  rw [hT]
  refine .lamA (.lamI ?_)
  rw [Fam_subst]
  exact hr

/-! ## Σ-formulas: truth implies realizability -/

inductive Sig : HA.Formula → Prop where
  | eq (a b : HA.Tm) : Sig (.eq a b)
  | bot : Sig .bot
  | and {φ ψ} : Sig φ → Sig ψ → Sig (.and φ ψ)
  | or {φ ψ} : Sig φ → Sig ψ → Sig (.or φ ψ)
  | ex {φ} : Sig φ → Sig (.ex φ)
  | ball {φ} (m : Nat) : Sig φ → Sig (ballF m φ)

theorem Sig.realize {φ : HA.Formula} (hφ : Sig φ) :
    ∀ e, sat e φ → ∀ D, ∃ r, D ⊢ r ⊩ toTF (numEnv e) φ := by
  induction hφ with
  | eq a b =>
    intro e h D
    refine ⟨zero, .refl ?_⟩
    have h' : eval e a = eval e b := h
    exact (tr_numEnv_conv e a).trans (h' ▸ (tr_numEnv_conv e b).symm)
  | bot => intro e h; exact h.elim
  | and _ _ ih₁ ih₂ =>
    intro e h D
    obtain ⟨r₁, h₁⟩ := ih₁ e h.1 D
    obtain ⟨r₂, h₂⟩ := ih₂ e h.2 D
    exact ⟨_, .pairC h₁ h₂⟩
  | or _ _ ih₁ ih₂ =>
    intro e h D
    rcases h with h | h
    · obtain ⟨r, hr⟩ := ih₁ e h D; exact ⟨_, .orI₁ _ hr⟩
    · obtain ⟨r, hr⟩ := ih₂ e h D; exact ⟨_, .orI₂ _ hr⟩
  | ex _ ih =>
    intro e h D
    obtain ⟨n, hn⟩ := h
    obtain ⟨r, hr⟩ := ih _ hn D
    refine ⟨_, .pairE (b := r) ((numeral_typed (Γ := []) n).toF (erase D)) ?_⟩
    rw [toTF_ex_inst]; exact hr
  | ball m _ ih =>
    intro e h D
    rw [sat_ballF] at h
    exact RJ.ball _ e m (fun n hn D => ih _ (h n hn) D) D

/-! ## Positive formulas: realizability implies truth -/

inductive Pos : HA.Formula → Prop where
  | eq (a b : HA.Tm) : Pos (.eq a b)
  | bot : Pos .bot
  | and {φ ψ} : Pos φ → Pos ψ → Pos (.and φ ψ)
  | or {φ ψ} : Pos φ → Pos ψ → Pos (.or φ ψ)
  | ex {φ} : Pos φ → Pos (.ex φ)
  | all {φ} : Pos φ → Pos (.all φ)
  | imp {φ ψ} : Sig φ → Pos ψ → Pos (.imp φ ψ)

/-- Close a realizer of a numeral instance. -/
theorem RJ.closeNum {r : Term} {φ : HA.Formula} {e : Nat → Nat}
    (h : D₀ ⊢ r ⊩ toTF (numEnv e) φ) :
    D₀ ⊢ psubst ρ₀ r ⊩ toTF (numEnv e) φ ∧ HasType [] (psubst ρ₀ r) (toTF (numEnv e) φ).ty := by
  have := RJ.close h
  rw [toTF_numEnv_subst] at this
  exact this

theorem Pos.sound (N : NatNorm) {φ : HA.Formula} (hφ : Pos φ) :
    ∀ e r, D₀ ⊢ r ⊩ toTF (numEnv e) φ → sat e φ := by
  induction hφ with
  | eq a b =>
    intro e r h
    obtain ⟨h₁, h₂⟩ := RJ.closeNum h
    have hc := RJ.eq_closed N h₁ h₂
    exact Conv.numeral_inj (((tr_numEnv_conv e a).symm.trans hc).trans (tr_numEnv_conv e b))
  | bot =>
    intro e r h
    obtain ⟨h₁, h₂⟩ := RJ.closeNum h
    obtain ⟨n, hn⟩ := N _ h₂
    exact no_numeral_bot (h₁.redStar hn)
  | and _ _ ih₁ ih₂ => intro e r h; exact ⟨ih₁ e _ (.fstC h), ih₂ e _ (.sndC h)⟩
  | or _ _ ih₁ ih₂ =>
    rename_i φ ψ _ _
    intro e r h
    obtain ⟨h₁, h₂⟩ := RJ.closeNum h
    simp only [toTF, orTF, TF.ty] at h₁ h₂
    obtain ⟨k, hk⟩ := N _ (.fst h₂)
    have hb := (RJ.sndE h₁).conv (TFConv.inst_conv _ (Conv.of_red hk))
    rw [orBody_inst] at hb
    cases k with
    | zero =>
      exact .inl (ih₁ e _ (.appI (.fstC hb) (.refl (Conv.refl _))))
    | succ k =>
      have hneg : D₀ ⊢ lam (rect (dflt TF.bot.ty) K' (Term.var 0)) ⊩
          .imp (.eq zero (numeral (k + 1))) TF.bot :=
        .lamI (RJ.botE' (c := numeral k) (.var (k := 0) (by
          simp only [ext, scons_zero, Entry.subst, TF.subst, psubst, psubst_numeral]; rfl)) TF.bot wk)
      exact .inr (ih₂ e _ (.appI (.sndC hb) hneg))
  | ex _ ih =>
    intro e r h
    obtain ⟨h₁, h₂⟩ := RJ.closeNum h
    simp only [toTF, TF.ty] at h₁ h₂
    obtain ⟨n, hn⟩ := N _ (.fst h₂)
    have hb := (RJ.sndE h₁).conv (TFConv.inst_conv _ (Conv.of_red hn))
    rw [toTF_ex_inst] at hb
    exact ⟨n, ih _ _ hb⟩
  | all _ ih =>
    intro e r h n
    simp only [toTF] at h
    have := RJ.appA h ((numeral_typed (Γ := []) n).toF (erase D₀))
    rw [toTF_ex_inst] at this
    exact ih _ _ this
  | imp hσ _ ih =>
    intro e r h hs
    obtain ⟨a, ha⟩ := hσ.realize e hs D₀
    exact ih e _ (.appI h ha)

end Rz
