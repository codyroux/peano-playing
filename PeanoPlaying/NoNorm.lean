import PeanoPlaying.EncodeSound
import PeanoPlaying.EncodeComplete

/-!
# HA does not prove normalization of System T

`NormStmt` is the HA sentence `∀c. ∃n. Typed(c) ⊃ Norm(c, n)` over Cantor
codes: every code of a closed term of type `nat` has a value. If HA proved
it, realizability would extract a T-term `E : nat ⟶ nat` computing that
value from the code. That term would be a self-evaluator, which
`no_self_evaluator` rules out.

1. `hsound` (through `forall_exists`) turns the proof into a closed
   `E : nat ⟶ nat`, together with, for each `c`, a realizer of
   `Typed(c) ⊃ Norm(c, m)`, where `E c ⟶* m`.
2. `Typed(c) ⊃ Norm(c, m)` is positive with a Σ antecedent, so its realizer
   makes it true (`Pos.sound`).
3. For `c = ⌜t⌝` with `t : nat` closed, `Typed(c)` is true
   (`typed_complete`), so `Norm(c, m)` is true, so `t ⇒* numeral m`
   (`norm_sound`). Hence `E ⌜t⌝` evaluates to the value of `t`.
-/

namespace Rz

open Term Ty

/-- **HA does not prove that closed terms of type `nat` have normal forms.** -/
theorem HA_not_proves_normalization : ¬ HA.Proves [] NormStmt := by
  intro h
  obtain ⟨E, hE, hspec⟩ := forall_exists natNorm (φ := .imp Typed Norm) h
  refine @no_self_evaluator cantorReasonable E ⟨hE, fun t n ht hn => ?_⟩
  show E ⬝ numeral (code t) ⇒* numeral n
  obtain ⟨m, hm, r, _, hr⟩ := hspec (code t)
  -- the extracted instance is true
  have hsat : sat (env2 m (code t)) (.imp Typed Norm) :=
    Pos.sound natNorm (Pos.imp sig_Typed pos_Norm) _ r hr
  -- so `t` normalizes to `m`
  have hred : t ⇒* numeral m := norm_sound (hsat (typed_complete ht m))
  have hnm : n = m := numeral_unique hn hred
  subst hnm
  -- and `E ⌜t⌝` evaluates to `m`
  obtain ⟨k, hk⟩ := normalize (HasType.app hE (numeral_typed (code t)))
  have hkm : k = n :=
    Conv.numeral_inj ((Conv.of_red (whnorm_redStar hk)).symm.trans (Conv.of_red hm))
  rw [← hkm]
  exact hk

end Rz
