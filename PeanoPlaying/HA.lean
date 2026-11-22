import PeanoPlaying.Basic

/-!
# Heyting Arithmetic: syntax

First-order arithmetic terms and formulas, with de Bruijn variables.
Substitutions are plain functions `Nat → Tm`; since arithmetic terms have
no binders, the only binders are the quantifiers of formulas.
-/

namespace HA

/-! ## Terms -/

inductive Tm where
| var : Nat → Tm
| zero : Tm
| succ : Tm → Tm
| add : Tm → Tm → Tm
| mul : Tm → Tm → Tm
deriving Repr, DecidableEq

namespace Tm

/-- Simultaneous substitution of terms for variables. -/
def subst (σ : Nat → Tm) : Tm → Tm
| var k => σ k
| zero => zero
| succ t => succ (subst σ t)
| add t u => add (subst σ t) (subst σ u)
| mul t u => mul (subst σ t) (subst σ u)

/-- The weakening substitution `k ↦ k + 1`. -/
def shift : Nat → Tm := fun k => var (k + 1)

/-- `t ⋅ σ`: extend `σ` with `t` for variable `0`, shifting the others down. -/
def scons (t : Tm) (σ : Nat → Tm) : Nat → Tm
| 0 => t
| k + 1 => σ k

/-- Substitution composition: first `σ`, then `τ`. -/
def comp (σ τ : Nat → Tm) : Nat → Tm := fun k => subst τ (σ k)

/-- Lift a substitution under a binder. -/
def up (σ : Nat → Tm) : Nat → Tm := scons (var 0) (comp σ shift)

/-- Substitute `u` for variable `0` (and decrement the others). -/
def inst (u : Tm) : Nat → Tm := scons u var

theorem subst_var (t : Tm) : subst var t = t := by
  induction t <;> simp_all [subst]

theorem subst_comp (σ τ : Nat → Tm) (t : Tm) :
    subst τ (subst σ t) = subst (comp σ τ) t := by
  induction t <;> simp_all [subst, comp]

theorem comp_shift_up (σ : Nat → Tm) : comp shift (up σ) = comp σ shift := by
  funext k; rfl

theorem up_comp (σ τ : Nat → Tm) : comp (up σ) (up τ) = up (comp σ τ) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show subst (up τ) (subst shift (σ k)) = subst shift (subst τ (σ k))
    rw [subst_comp, subst_comp, comp_shift_up]

theorem up_var : up var = var := by
  funext k; cases k <;> rfl

end Tm

/-! ## Formulas -/

inductive Formula where
| eq : Tm → Tm → Formula
| bot : Formula
| and : Formula → Formula → Formula
| or : Formula → Formula → Formula
| imp : Formula → Formula → Formula
| ex : Formula → Formula
| all : Formula → Formula
deriving Repr, DecidableEq

namespace Formula

/-- Simultaneous substitution, lifted under quantifiers. -/
def subst (σ : Nat → Tm) : Formula → Formula
| eq t u => eq (t.subst σ) (u.subst σ)
| bot => bot
| and φ ψ => and (subst σ φ) (subst σ ψ)
| or φ ψ => or (subst σ φ) (subst σ ψ)
| imp φ ψ => imp (subst σ φ) (subst σ ψ)
| ex φ => ex (subst (Tm.up σ) φ)
| all φ => all (subst (Tm.up σ) φ)

/-- Weakening: shift all free variables up by one. -/
def lift (φ : Formula) : Formula := subst Tm.shift φ

/-- `φ[u]`: substitute `u` for variable `0` of `φ`. -/
def inst (φ : Formula) (u : Tm) : Formula := subst (Tm.inst u) φ

def neg (φ : Formula) : Formula := imp φ bot

def iff (φ ψ : Formula) : Formula := and (imp φ ψ) (imp ψ φ)

theorem subst_var (φ : Formula) : subst Tm.var φ = φ := by
  induction φ <;> simp_all [subst, Tm.subst_var, Tm.up_var]

theorem subst_comp (σ τ : Nat → Tm) (φ : Formula) :
    subst τ (subst σ φ) = subst (Tm.comp σ τ) φ := by
  induction φ generalizing σ τ <;> simp_all [subst, Tm.subst_comp, Tm.up_comp]

/-- Instantiating a lifted formula gives it back. -/
theorem lift_inst (φ : Formula) (u : Tm) : (lift φ).inst u = φ := by
  simp only [lift, inst, subst_comp]
  exact subst_var φ

end Formula

/-! ## Notation -/

scoped infix:50 " ≐ " => Formula.eq
scoped notation "⊥'" => Formula.bot
scoped infixr:35 " ⋏ " => Formula.and
scoped infixr:30 " ⋎ " => Formula.or
scoped infixr:25 " ⊃ " => Formula.imp
scoped prefix:max "∃'" => Formula.ex
scoped prefix:max "∀'" => Formula.all
scoped prefix:max "¬'" => Formula.neg

open Tm in
/-- Example: `∀x. ∃y. x + y ≐ S x`. -/
example : Formula := ∀' (∃' (add (var 1) (var 0) ≐ succ (var 1)))

open Tm in
#eval ((∃' (add (var 1) (var 0) ≐ zero)).inst (succ zero) : Formula)

/-! ## Proof rules

Natural deduction with a list of hypotheses `Γ`. Free term variables are
implicit: going under a binder (`∀`-introduction, `∃`-elimination) shifts the
hypotheses with `lift`, so that variable `0` is the fresh eigenvariable. -/

/-- Weakening of terms. -/
def Tm.lift (t : Tm) : Tm := t.subst Tm.shift

theorem Tm.lift_inst (t u : Tm) : (Tm.lift t).subst (Tm.inst u) = t := by
  rw [Tm.lift, Tm.subst_comp]
  exact Tm.subst_var t

@[simp] theorem Tm.lift_scons (t u : Tm) : (Tm.lift t).subst (Tm.scons u Tm.var) = t :=
  Tm.lift_inst t u

/-- `φ(S x)` from `φ(x)`, where `x` is variable `0`. -/
def Formula.succInst (φ : Formula) : Formula :=
  φ.subst (Tm.scons (Tm.succ (Tm.var 0)) Tm.shift)

open Tm Formula in
inductive Proves : List Formula → Formula → Prop where
-- structural
| hyp : φ ∈ Γ → Proves Γ φ
-- conjunction
| andI : Proves Γ φ → Proves Γ ψ → Proves Γ (φ ⋏ ψ)
| andE₁ : Proves Γ (φ ⋏ ψ) → Proves Γ φ
| andE₂ : Proves Γ (φ ⋏ ψ) → Proves Γ ψ
-- disjunction
| orI₁ : Proves Γ φ → Proves Γ (φ ⋎ ψ)
| orI₂ : Proves Γ ψ → Proves Γ (φ ⋎ ψ)
| orE : Proves Γ (φ ⋎ ψ) → Proves (φ :: Γ) χ → Proves (ψ :: Γ) χ → Proves Γ χ
-- implication
| impI : Proves (φ :: Γ) ψ → Proves Γ (φ ⊃ ψ)
| impE : Proves Γ (φ ⊃ ψ) → Proves Γ φ → Proves Γ ψ
-- absurdity
| botE : Proves Γ ⊥' → Proves Γ φ
-- quantifiers
| allI : Proves (Γ.map lift) φ → Proves Γ (∀' φ)
| allE : Proves Γ (∀' φ) → Proves Γ (Formula.inst φ t)
| exI : Proves Γ (Formula.inst φ t) → Proves Γ (∃' φ)
| exE : Proves Γ (∃' φ) → Proves (φ :: Γ.map lift) (lift ψ) → Proves Γ ψ
-- equality
| refl : Proves Γ (t ≐ t)
| eqSubst : Proves Γ (t ≐ u) → Proves Γ (Formula.inst φ t) → Proves Γ (Formula.inst φ u)
-- arithmetic
| zero_ne_succ : Proves Γ (zero ≐ succ t) → Proves Γ ⊥'
| succ_inj : Proves Γ (succ t ≐ succ u) → Proves Γ (t ≐ u)
| add_zero : Proves Γ (add t zero ≐ t)
| add_succ : Proves Γ (add t (succ u) ≐ succ (add t u))
| mul_zero : Proves Γ (mul t zero ≐ zero)
| mul_succ : Proves Γ (mul t (succ u) ≐ add (mul t u) t)
-- induction on variable `0` of `φ`
| ind : Proves Γ (Formula.inst φ zero) → Proves Γ (∀' (φ ⊃ Formula.succInst φ)) → Proves Γ (∀' φ)

scoped infix:20 " ⊢ₕ " => Proves

/-! ### Derived rules and a sanity check -/

theorem Proves.symm {Γ : List Formula} {t u : Tm} (h : Γ ⊢ₕ t ≐ u) : Γ ⊢ₕ u ≐ t := by
  have := Proves.eqSubst (φ := Tm.var 0 ≐ t.lift) h
    (by simp only [Formula.inst, Formula.subst, Tm.subst, Tm.inst, Tm.scons, Tm.lift_scons]
        exact Proves.refl)
  simpa only [Formula.inst, Formula.subst, Tm.subst, Tm.inst, Tm.scons, Tm.lift_scons] using this

theorem Proves.trans {Γ : List Formula} {t u v : Tm}
    (h₁ : Γ ⊢ₕ t ≐ u) (h₂ : Γ ⊢ₕ u ≐ v) : Γ ⊢ₕ t ≐ v := by
  have := Proves.eqSubst (φ := t.lift ≐ Tm.var 0) h₂
    (by simpa only [Formula.inst, Formula.subst, Tm.subst, Tm.inst, Tm.scons, Tm.lift_scons]
          using h₁)
  simpa only [Formula.inst, Formula.subst, Tm.subst, Tm.inst, Tm.scons, Tm.lift_scons] using this

open Tm in
/-- `⊢ ∀x. 0 + x = x`, by induction. -/
example : [] ⊢ₕ ∀' (add zero (var 0) ≐ var 0) := by
  apply Proves.ind
  · exact Proves.add_zero
  · apply Proves.allI
    apply Proves.impI
    -- goal: [0 + x = x] ⊢ 0 + S x = S x
    refine Proves.trans Proves.add_succ ?_
    -- rewrite `0 + x` to `x` under `succ`
    exact Proves.eqSubst (φ := succ (add zero (var 1)) ≐ succ (var 0))
      (Proves.hyp (List.mem_singleton.mpr rfl)) Proves.refl

end HA
