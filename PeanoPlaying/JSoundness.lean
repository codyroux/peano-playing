import PeanoPlaying.Judgment

/-!
# Soundness of HA for the inductive realizability judgment

`hsound`: every HA derivation `Γ ⊢ φ` gives a T-term `t` with `D ⊢ t ⊩ ⟦φ⟧ρ`,
in any context `D` that realizes the hypotheses `Γ` under the environment `ρ`.
This step is purely syntactic: it does not use normalization.

Normalization enters only afterwards, together with subject reduction:

1. `consistency_of_normalization`: a closed realizer of `⊥` erases to a
   closed `nat` term. By `NatNorm` it reduces to a numeral, which still
   realizes `⊥` by subject reduction, and no numeral does (`no_numeral_bot`).
2. `forall_exists` and `forall_exists_eq`: a proof of `∀x ∃y φ` gives a
   T-definable `f : nat ⟶ nat` such that `RJ` derives `φ(n, f n)`. For
   equations, this means `φ(n, f n)` is true.

Every ingredient is an inductive relation on finite syntax (`RJ`, `HasType`,
`Red`), so these statements can be formalized in HA itself.
-/

namespace Rz

open Term Ty

/-! ## Translating HA formulas -/

/-- The body of the disjunction encoding:
`(0 = x ⊃ A) ∧ (¬ 0 = x ⊃ B)` with `x` variable `0`. -/
def orBody (A B : TF) : TF :=
  .and (.imp (.eq zero (Term.var 0)) (A.subst wk)) (.imp (.imp (.eq zero (Term.var 0)) TF.bot) (B.subst wk))

/-- `A ∨ B := ∃x. (0 = x ⊃ A) ∧ (¬ 0 = x ⊃ B)`. -/
def orTF (A B : TF) : TF := .ex (orBody A B)

def toTF (ρ : Nat → Term) : HA.Formula → TF
  | .eq a b => .eq (tr ρ a) (tr ρ b)
  | .bot => TF.bot
  | .and φ ψ => .and (toTF ρ φ) (toTF ρ ψ)
  | .or φ ψ => orTF (toTF ρ φ) (toTF ρ ψ)
  | .imp φ ψ => .imp (toTF ρ φ) (toTF ρ ψ)
  | .ex φ => .ex (toTF (up ρ) φ)
  | .all φ => .all (toTF (up ρ) φ)

theorem orBody_inst (A B : TF) (a : Term) :
    (orBody A B).inst a = .and (.imp (.eq zero a) A) (.imp (.imp (.eq zero a) TF.bot) B) := by
  simp only [orBody, TF.inst, TF.subst, psubst, scons_zero, TF.bot_subst]
  rw [← TF.inst, ← TF.inst, TF.wk_inst, TF.wk_inst]

theorem orBody_subst_up (A B : TF) (σ : Nat → Term) :
    (orBody A B).subst (up σ) = orBody (A.subst σ) (B.subst σ) := by
  simp only [orBody, TF.subst, psubst, up_zero, TF.bot_subst, TF.wk_up]

theorem toTF_subst (φ : HA.Formula) : ∀ (ρ σ : Nat → Term),
    (toTF ρ φ).subst σ = toTF (fun k => psubst σ (ρ k)) φ := by
  induction φ with
  | eq a b => intro ρ σ; simp only [toTF, TF.subst, psubst_tr]
  | bot => intro ρ σ; rfl
  | and φ ψ ih₁ ih₂ => intro ρ σ; simp only [toTF, TF.subst, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro ρ σ; simp only [toTF, orTF, TF.subst, orBody_subst_up, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => intro ρ σ; simp only [toTF, TF.subst, ih₁, ih₂]
  | ex φ ih => intro ρ σ; simp only [toTF, TF.subst, ih, up_comp]
  | all φ ih => intro ρ σ; simp only [toTF, TF.subst, ih, up_comp]

theorem toTF_wk (ρ : Nat → Term) (φ : HA.Formula) :
    toTF (fun k => psubst wk (ρ k)) φ = (toTF ρ φ).subst wk := (toTF_subst φ ρ wk).symm

theorem tr_up_eq (ρ : Nat → Term) (τ : Nat → HA.Tm) :
    (fun k => tr (up ρ) (HA.Tm.up τ k)) = up (fun k => tr ρ (τ k)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show tr (up ρ) ((τ k).subst HA.Tm.shift) = sh (tr ρ (τ k))
    rw [tr_subst, sh_eq, psubst_tr]
    congr 1
    funext j
    exact sh_eq (ρ j)

theorem toTF_hsubst (φ : HA.Formula) : ∀ (ρ : Nat → Term) (τ : Nat → HA.Tm),
    toTF ρ (φ.subst τ) = toTF (fun k => tr ρ (τ k)) φ := by
  induction φ with
  | eq a b => intro ρ τ; simp only [HA.Formula.subst, toTF, tr_subst]
  | bot => intro ρ τ; rfl
  | and φ ψ ih₁ ih₂ => intro ρ τ; simp only [HA.Formula.subst, toTF, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro ρ τ; simp only [HA.Formula.subst, toTF, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => intro ρ τ; simp only [HA.Formula.subst, toTF, ih₁, ih₂]
  | ex φ ih => intro ρ τ; simp only [HA.Formula.subst, toTF, ih, tr_up_eq]
  | all φ ih => intro ρ τ; simp only [HA.Formula.subst, toTF, ih, tr_up_eq]

theorem toTF_lift (ρ : Nat → Term) (ψ : HA.Formula) :
    toTF (up ρ) ψ.lift = (toTF ρ ψ).subst wk := by
  rw [HA.Formula.lift, toTF_hsubst, toTF_subst]
  congr 1
  funext k
  exact sh_eq (ρ k)

theorem toTF_lift_inst (ρ : Nat → Term) (ψ : HA.Formula) (a : Term) :
    (toTF (up ρ) ψ.lift).inst a = toTF ρ ψ := by
  rw [toTF_lift, TF.wk_inst]

theorem toTF_inst (ρ : Nat → Term) (φ : HA.Formula) (u : HA.Tm) :
    toTF ρ (φ.inst u) = (toTF (up ρ) φ).inst (tr ρ u) := by
  rw [HA.Formula.inst, toTF_hsubst, TF.inst, toTF_subst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show ρ k = psubst (scons (tr ρ u) Term.var) (sh (ρ k))
    rw [psubst_sh_scons, psubst_var]

theorem toTF_succInst (ρ : Nat → Term) (φ : HA.Formula) :
    toTF (up ρ) φ.succInst = (toTF (up ρ) φ).subst TF.succσ := by
  rw [HA.Formula.succInst, toTF_hsubst, toTF_subst]
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show sh (ρ k) = psubst (scons (succ (Term.var 0)) wk) (sh (ρ k))
    rw [psubst_sh_scons, sh_eq]

/-! ## Derived rules -/

/-- Induction as a closed realizer of `∀x A(x)`. -/
theorem RJ.indAll {D : Ctx} {z s : Term} {A : TF} (hz : D ⊢ z ⊩ A.inst zero)
    (hs : D ⊢ s ⊩ .all (.imp A (A.subst TF.succσ))) :
    D ⊢ lam (rect (psubst wk z) (psubst wk s) (Term.var 0)) ⊩ .all A := by
  refine .lamA ?_
  have hz' := hz.weaken .obj
  rw [TF.inst_subst] at hz'
  have hs' := hs.weaken .obj
  simp only [TF.subst] at hs'
  rw [TF.succ_up] at hs'
  have h := RJ.ind (A := A.subst (up wk)) hz' hs' (HasTypeF.var' (n := 0) rfl)
  rwa [TF.upwk_inst_var] at h

/-- `fun _ acc => acc`, the predecessor's step function. -/
def predS : Term := lam (lam (Term.var 1))

theorem red_pred (x : Term) : rect zero predS (succ x) ⟶* x :=
  .step .rects (red_beta2 (Term.var 1) _ _)

theorem RJ.succInj {D : Ctx} {e a b : Term} (he : D ⊢ e ⊩ .eq (succ a) (succ b)) :
    D ⊢ rect zero K' e ⊩ .eq a b := by
  have hM : ∀ x, (TF.eq (psubst wk a) (rect zero predS (Term.var 0))).inst x = .eq a (rect zero predS x) := by
    intro x
    simp only [TF.inst, TF.subst, psubst, psubst_wk_scons, psubst_var]
    rfl
  have h0 : D ⊢ zero ⊩ (TF.eq (psubst wk a) (rect zero predS (Term.var 0))).inst (succ a) := by
    rw [hM]; exact .refl (Conv.of_red (red_pred a)).symm
  have h1 := RJ.eqElim he h0
  rw [hM] at h1
  exact h1.conv (TFConv.eq_iff.mpr ⟨Conv.refl _, Conv.of_red (red_pred b)⟩)

theorem RJ.orI₁ {D : Ctx} {t : Term} {A : TF} (B : TF) (h : D ⊢ t ⊩ A) :
    D ⊢ pair zero (pair (lam (psubst wk t)) (lam (rect (dflt B.ty) K' (app (Term.var 0) zero)))) ⊩
      orTF A B := by
  refine .pairE .zero ?_
  rw [orBody_inst]
  refine .pairC (.lamI (h.weaken _)) (.lamI ?_)
  have he : ext (.prf (.imp (.eq zero zero) TF.bot)) D ⊢ app (Term.var 0) zero ⊩ TF.bot :=
    .appI (.var (k := 0) rfl) (.refl (Conv.refl zero))
  exact RJ.botE' (c := zero) he B wk

theorem RJ.orI₂ {D : Ctx} {t : Term} {B : TF} (A : TF) (h : D ⊢ t ⊩ B) :
    D ⊢ pair (succ zero) (pair (lam (rect (dflt A.ty) K' (Term.var 0))) (lam (psubst wk t))) ⊩
      orTF A B := by
  refine .pairE (.succ .zero) ?_
  rw [orBody_inst]
  refine .pairC (.lamI ?_) (.lamI (h.weaken _))
  have he : ext (.prf (.eq zero (succ zero))) D ⊢ Term.var 0 ⊩ TF.bot := .var (k := 0) rfl
  exact RJ.botE' (c := zero) he A wk

/-- Three weakenings. -/
def w3 : Nat → Term := fun k => Term.var (k + 3)

theorem orBody_S (A B : TF) :
    (((orBody A B).subst TF.succσ).subst wk).subst wk =
      .and (.imp (.eq zero (succ (Term.var 2))) (A.subst w3))
        (.imp (.imp (.eq zero (succ (Term.var 2))) TF.bot) (B.subst w3)) := by
  simp only [orBody, TF.subst, psubst, TF.bot_subst, TF.subst_subst]
  rfl

theorem RJ.orE {D : Ctx} {p c₁ c₂ : Term} {A B C : TF} (hp : D ⊢ p ⊩ orTF A B)
    (h₁ : ext (.prf A) D ⊢ c₁ ⊩ C.subst wk) (h₂ : ext (.prf B) D ⊢ c₂ ⊩ C.subst wk) :
    ∃ t, D ⊢ t ⊩ C := by
  -- The motive, with the tag as variable `0`.
  have hfst : HasTypeF (Rz.erase D) (fst p) nat := .fst hp.erase
  -- Base case: tag `0`, use the left branch.
  have hZ : D ⊢ lam (psubst (scons (app (fst (Term.var 0)) zero) wk) c₁) ⊩
      (TF.imp (orBody A B) (C.subst wk)).inst zero := by
    show D ⊢ _ ⊩ .imp ((orBody A B).inst zero) ((C.subst wk).inst zero)
    rw [orBody_inst, TF.wk_inst]
    refine .lamI ?_
    have hh : ext (.prf (.and (.imp (.eq zero zero) A) (.imp (.imp (.eq zero zero) TF.bot) B))) D ⊢
        app (fst (Term.var 0)) zero ⊩ A.subst wk :=
      .appI (.fstC (.var (k := 0) rfl)) (.refl (Conv.refl _))
    have := h₁.subst ((SubstOK.wk _).cons hh)
    rwa [TF.subst_wk_scons] at this
  -- Step case: tag `S m`, use the right branch.
  have hS : D ⊢ lam (lam (lam (psubst (scons (app (snd (Term.var 0))
        (lam (rect (dflt nat) K' (Term.var 0)))) w3) c₂))) ⊩
      .all (.imp (TF.imp (orBody A B) (C.subst wk))
        ((TF.imp (orBody A B) (C.subst wk)).subst TF.succσ)) := by
    refine .lamA (.lamI (.lamI ?_))
    -- the context after the three binders
    have hσ : SubstOK D (ext (.prf (((orBody A B).subst TF.succσ).subst wk))
        (ext (.prf (TF.imp (orBody A B) (C.subst wk))) (ext .obj D))) w3 :=
      ((SubstOK.wk _).comp (SubstOK.wk _)).comp (SubstOK.wk _)
    have hneg : ext (.prf (((orBody A B).subst TF.succσ).subst wk))
        (ext (.prf (TF.imp (orBody A B) (C.subst wk))) (ext .obj D)) ⊢
        lam (rect (dflt nat) K' (Term.var 0)) ⊩ .imp (.eq zero (succ (Term.var 2))) TF.bot := by
      refine .lamI ?_
      exact RJ.botE' (.var (k := 0) rfl) TF.bot wk
    have hv : ext (.prf (((orBody A B).subst TF.succσ).subst wk))
        (ext (.prf (TF.imp (orBody A B) (C.subst wk))) (ext .obj D)) ⊢ Term.var 0 ⊩
        .and (.imp (.eq zero (succ (Term.var 2))) (A.subst w3))
          (.imp (.imp (.eq zero (succ (Term.var 2))) TF.bot) (B.subst w3)) := by
      refine .var ?_
      show Entry.prf ((((orBody A B).subst TF.succσ).subst wk).subst wk) = _
      rw [orBody_S]
    have hh := RJ.appI (RJ.sndC hv) hneg
    have := h₂.subst (hσ.cons hh)
    rw [TF.subst_wk_scons] at this
    have e : ((((C.subst wk).subst TF.succσ).subst wk).subst wk) = C.subst w3 := by
      simp only [TF.subst_subst]; rfl
    show _ ⊢ _ ⊩ (((C.subst wk).subst TF.succσ).subst wk).subst wk
    rw [e]
    exact this
  have hR := RJ.ind hZ hS hfst
  have hres : D ⊢ app (rect _ _ (fst p)) (snd p) ⊩ (C.subst wk).inst (fst p) :=
    RJ.appI hR (RJ.sndE hp)
  rw [TF.wk_inst] at hres
  exact ⟨_, hres⟩

/-! ## Soundness -/

/-- `D` realizes the hypotheses `Γ`, with HA variables read in `ρ`. -/
structure CtxOK (D : Ctx) (ρ : Nat → Term) (Γ : List HA.Formula) : Prop where
  env : ∀ k, HasTypeF (erase D) (ρ k) nat
  hyp : ∀ ψ ∈ Γ, ∃ h, D ⊢ h ⊩ toTF ρ ψ

theorem CtxOK.weak {D : Ctx} {ρ : Nat → Term} {Γ : List HA.Formula} (h : CtxOK D ρ Γ)
    (e : Entry) : CtxOK (ext e D) (fun k => psubst wk (ρ k)) Γ where
  env k := by
    rw [erase_ext, ← sh_eq]
    exact (h.env k).sh
  hyp ψ hψ := by
    obtain ⟨u, hu⟩ := h.hyp ψ hψ
    exact ⟨_, by rw [toTF_wk]; exact hu.weaken e⟩

theorem CtxOK.cons {D : Ctx} {ρ : Nat → Term} {Γ : List HA.Formula} (h : CtxOK D ρ Γ)
    (φ : HA.Formula) :
    CtxOK (ext (.prf (toTF ρ φ)) D) (fun k => psubst wk (ρ k)) (φ :: Γ) where
  env := (h.weak _).env
  hyp ψ hψ := by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact ⟨Term.var 0, by rw [toTF_wk]; exact .var (k := 0) rfl⟩
    · exact (h.weak _).hyp ψ hψ

theorem CtxOK.bind {D : Ctx} {ρ : Nat → Term} {Γ : List HA.Formula} (h : CtxOK D ρ Γ) :
    CtxOK (ext .obj D) (up ρ) (Γ.map HA.Formula.lift) where
  env k := by
    rw [erase_ext]
    cases k with
    | zero => exact .var
    | succ k => exact (h.env k).sh
  hyp ψ' hψ' := by
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hψ'
    obtain ⟨u, hu⟩ := h.hyp ψ hψ
    exact ⟨_, by rw [toTF_lift]; exact hu.weaken .obj⟩

/-- **Soundness**, without any normalization hypothesis. -/
theorem hsound {Γ : List HA.Formula} {φ : HA.Formula} (h : HA.Proves Γ φ) :
    ∀ {D ρ}, CtxOK D ρ Γ → ∃ t, D ⊢ t ⊩ toTF ρ φ := by
  induction h with
  | hyp hm => intro D ρ hc; exact hc.hyp _ hm
  | andI _ _ ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨_, h₁⟩ := ih₁ hc; obtain ⟨_, h₂⟩ := ih₂ hc
    exact ⟨_, .pairC h₁ h₂⟩
  | andE₁ _ ih => intro D ρ hc; obtain ⟨_, h⟩ := ih hc; exact ⟨_, .fstC h⟩
  | andE₂ _ ih => intro D ρ hc; obtain ⟨_, h⟩ := ih hc; exact ⟨_, .sndC h⟩
  | orI₁ _ ih => intro D ρ hc; obtain ⟨_, h⟩ := ih hc; exact ⟨_, .orI₁ _ h⟩
  | orI₂ _ ih => intro D ρ hc; obtain ⟨_, h⟩ := ih hc; exact ⟨_, .orI₂ _ h⟩
  | orE _ _ _ ih ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨_, hp⟩ := ih hc
    obtain ⟨_, h₁⟩ := ih₁ (hc.cons _)
    obtain ⟨_, h₂⟩ := ih₂ (hc.cons _)
    rw [toTF_wk] at h₁ h₂
    exact RJ.orE hp h₁ h₂
  | impI _ ih =>
    intro D ρ hc
    obtain ⟨_, h⟩ := ih (hc.cons _)
    rw [toTF_wk] at h
    exact ⟨_, .lamI h⟩
  | impE _ _ ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨_, h₁⟩ := ih₁ hc; obtain ⟨_, h₂⟩ := ih₂ hc
    exact ⟨_, .appI h₁ h₂⟩
  | botE _ ih =>
    intro D ρ hc
    obtain ⟨_, h⟩ := ih hc
    exact ⟨_, RJ.botE (c := zero) h⟩
  | allI _ ih =>
    intro D ρ hc
    obtain ⟨_, h⟩ := ih hc.bind
    exact ⟨_, .lamA h⟩
  | allE _ ih =>
    intro D ρ hc
    obtain ⟨_, h⟩ := ih hc
    exact ⟨_, by rw [toTF_inst]; exact RJ.appA h (tr_typedF hc.env _)⟩
  | exI _ ih =>
    intro D ρ hc
    obtain ⟨_, h⟩ := ih hc
    rw [toTF_inst] at h
    exact ⟨_, .pairE (tr_typedF hc.env _) h⟩
  | @exE _ φ ψ _ _ ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨p, hp⟩ := ih₁ hc
    obtain ⟨e, he⟩ := ih₂ (hc.bind.cons _)
    rw [toTF_wk] at he
    have hL : D ⊢ lam (lam e) ⊩ .all (.imp (toTF (up ρ) φ) (toTF (up ρ) ψ.lift)) :=
      .lamA (.lamI he)
    have hres : D ⊢ app (app (lam (lam e)) (fst p)) (snd p) ⊩ (toTF (up ρ) ψ.lift).inst (fst p) :=
      RJ.appI (RJ.appA hL (.fst hp.erase)) (RJ.sndE hp)
    rw [toTF_lift_inst] at hres
    exact ⟨_, hres⟩
  | refl => intro D ρ hc; exact ⟨_, .refl (Conv.refl _)⟩
  | eqSubst _ _ ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨_, he⟩ := ih₁ hc; obtain ⟨_, hx⟩ := ih₂ hc
    rw [toTF_inst] at hx
    exact ⟨_, by rw [toTF_inst]; exact .eqElim he hx⟩
  | zero_ne_succ _ ih =>
    intro D ρ hc
    obtain ⟨_, he⟩ := ih hc
    exact ⟨_, RJ.botE (A := TF.bot) he⟩
  | succ_inj _ ih =>
    intro D ρ hc
    obtain ⟨_, he⟩ := ih hc
    exact ⟨_, RJ.succInj he⟩
  | add_zero => intro D ρ hc; exact ⟨_, .refl (Conv.of_red (red_add_zero _))⟩
  | add_succ => intro D ρ hc; exact ⟨_, .refl (Conv.of_red (red_add_succ _ _))⟩
  | mul_zero => intro D ρ hc; exact ⟨_, .refl (Conv.of_red (red_mul_zero _))⟩
  | mul_succ => intro D ρ hc; exact ⟨_, .refl (Conv.of_red (red_mul_succ _ _))⟩
  | ind _ _ ih₁ ih₂ =>
    intro D ρ hc
    obtain ⟨_, hz⟩ := ih₁ hc; obtain ⟨_, hs⟩ := ih₂ hc
    rw [toTF_inst] at hz
    simp only [toTF] at hs
    rw [toTF_succInst] at hs
    exact ⟨_, RJ.indAll hz hs⟩

/-! ## Closed realizers -/

/-- The empty context: every variable is an object variable. -/
def D₀ : Ctx := fun _ => .obj

/-- The constant environment `0`. -/
def ρ₀ : Nat → Term := fun _ => zero

theorem CtxOK.nil : CtxOK D₀ ρ₀ [] := ⟨fun _ => .zero, fun _ h => absurd h List.not_mem_nil⟩

theorem SubstOK.zeros : SubstOK D₀ D₀ ρ₀ :=
  ⟨fun _ => .zero, fun _ _ h => by simp [D₀] at h⟩

/-- Close a realizer by sending its free (object) variables to `0`. -/
theorem RJ.close {t : Term} {A : TF} (h : D₀ ⊢ t ⊩ A) :
    D₀ ⊢ psubst ρ₀ t ⊩ A.subst ρ₀ ∧ HasType [] (psubst ρ₀ t) A.ty :=
  ⟨h.subst SubstOK.zeros, h.erase.psubst_list [] ρ₀ (fun _ => .zero)⟩

theorem toTF_ρ₀ (φ : HA.Formula) : (toTF ρ₀ φ).subst ρ₀ = toTF ρ₀ φ := by
  rw [toTF_subst]; rfl

/-- A closed realizer of an equation, after normalization, proves it. -/
theorem RJ.eq_closed (N : NatNorm) {r a b : Term} (h : D₀ ⊢ r ⊩ .eq a b)
    (hr : HasType [] r nat) : Conv a b := by
  obtain ⟨n, hn⟩ := N r hr
  exact (h.redStar hn).numeral_inv

/-! ## 1. Normalization implies consistency -/

theorem consistency_of_normalization (N : NatNorm) : ¬ HA.Proves [] .bot := by
  intro h
  obtain ⟨t, ht⟩ := hsound h CtxOK.nil
  obtain ⟨h₁, h₂⟩ := RJ.close ht
  obtain ⟨n, hn⟩ := N _ h₂
  exact no_numeral_bot (h₁.redStar hn)

theorem HA_consistent : ¬ HA.Proves [] .bot := consistency_of_normalization natNorm

/-! ## 2. `∀∃` theorems give T-definable functions -/

/-- Numerals for a standard environment. -/
def numEnv (e : Nat → Nat) : Nat → Term := fun k => numeral (e k)

/-- The standard environment `y ↦ m, x ↦ n`, all other variables `0`. -/
def env2 (m n : Nat) : Nat → Nat := scons m (scons n (fun _ => 0))

theorem forall_exists (N : NatNorm) {φ : HA.Formula} (h : HA.Proves [] (.all (.ex φ))) :
    ∃ f, HasType [] f (nat ⟶ nat) ∧ ∀ n : Nat, ∃ m : Nat,
      app f (numeral n) ⟶* numeral m ∧
      ∃ r, HasType [] r (toTF (numEnv (env2 m n)) φ).ty ∧
        D₀ ⊢ r ⊩ toTF (numEnv (env2 m n)) φ := by
  obtain ⟨t, ht⟩ := hsound h CtxOK.nil
  obtain ⟨h₁, h₂⟩ := RJ.close ht
  rw [toTF_ρ₀] at h₁
  generalize psubst ρ₀ t = T at h₁ h₂
  simp only [toTF, TF.ty] at h₁ h₂
  refine ⟨lam (fst (app (sh T) (Term.var 0))),
    .lam (.fst (.app h₂.sh (HasType.var (n := 0) (Γ := [nat]) (by simp)))), fun n => ?_⟩
  have hA := RJ.appA h₁ ((numeral_typed (Γ := []) n).toF (erase D₀))
  have hS := RJ.sndE hA
  have hfT : HasType [] (fst (app T (numeral n))) nat := .fst (.app h₂ (numeral_typed n))
  obtain ⟨m, hm⟩ := N _ hfT
  have hβ : app (lam (fst (app (sh T) (Term.var 0)))) (numeral n) ⟶* fst (app T (numeral n)) := by
    have := red_beta_psubst Term.var (fst (app (sh T) (Term.var 0))) (numeral n)
    rw [psubst_var] at this
    refine .single ?_
    simpa [psubst, psubst_var] using this
  -- the formula, computed
  have hF : ((toTF (up (up ρ₀)) φ).subst (up (scons (numeral n) Term.var))).inst (numeral m) =
      toTF (numEnv (env2 m n)) φ := by
    rw [TF.inst, TF.subst_subst, toTF_subst]
    congr 1
    funext k
    rcases k with _ | _ | k
    · rfl
    · show psubst (scons (numeral m) Term.var) (sh (numeral n)) = numeral n
      rw [psubst_sh_scons, psubst_numeral]
    · rfl
  refine ⟨m, ((Conv.of_red hβ).trans (Conv.of_red hm)).to_numeral, snd (app T (numeral n)), ?_, ?_⟩
  · rw [← hF, TF.inst, TF.ty_subst, TF.ty_subst]
    exact .snd (.app h₂ (numeral_typed n))
  · rw [← hF]
    exact hS.conv (TFConv.inst_conv _ (Conv.of_red hm))

/-- For equations, the realized instance is true in the standard model. -/
theorem forall_exists_eq (N : NatNorm) {a b : HA.Tm} (h : HA.Proves [] (.all (.ex (.eq a b)))) :
    ∃ f, HasType [] f (nat ⟶ nat) ∧ ∀ n : Nat, ∃ m : Nat,
      app f (numeral n) ⟶* numeral m ∧ eval (env2 m n) a = eval (env2 m n) b := by
  obtain ⟨f, hf, hspec⟩ := forall_exists N h
  refine ⟨f, hf, fun n => ?_⟩
  obtain ⟨m, hm, r, hrT, hr⟩ := hspec n
  refine ⟨m, hm, ?_⟩
  have hc := RJ.eq_closed N hr hrT
  exact Conv.numeral_inj
    (((Conv.of_red (tr_eval _ a)).symm.trans hc).trans (Conv.of_red (tr_eval _ b)))

end Rz
