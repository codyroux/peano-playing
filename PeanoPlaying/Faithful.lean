import PeanoPlaying.EncodeSound
import PeanoPlaying.EncodeComplete
import PeanoPlaying.NoNorm

/-!
# Faithfulness of the encoding, and truth of `NormStmt`

`EncodeSound` and `EncodeComplete` give the two directions of the encoding
that the unprovability proof uses. Here are the other two:

* `typed_sound`: if `Typed(c)` is true, then `c` codes a closed term of type
  `nat`. Numbers are decoded into types and contexts (`decTy`, `decCtx`),
  sending numbers that code no type to `nat`; a typing fact of a derivation
  table then becomes an actual typing judgment, by induction on its index.
* `norm_complete`: if `t ⇒* numeral m`, then `Norm(⌜t⌝, m)` is true. We build
  tables for every shifting, substitution, weak-head step and numeral.

Together with `normalize`, they show that `NormStmt` is true
(`normStmt_true`), and hence, with `HA_not_proves_normalization`, true but
not provable in HA.
-/

namespace Rz

open Term

/-! ## Unpairing -/

/-- The inverse of the Cantor pairing, by enumerating pairs in order. -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    match unpair n with
    | (0, b) => (b + 1, 0)
    | (a + 1, b) => (a, b + 1)

theorem npair_unpair : ∀ n, npair (unpair n).1 (unpair n).2 = n
  | 0 => rfl
  | n + 1 => by
    have ih := npair_unpair n
    rcases h : unpair n with ⟨_ | a, b⟩ <;> rw [h] at ih <;> simp only [unpair, h]
    · simp only [npair, tri, Nat.zero_add, Nat.add_zero] at ih ⊢; omega
    · dsimp only at ih
      unfold npair at ih ⊢
      rw [show a + (b + 1) = a + 1 + b by omega]; omega

theorem unpair_npair (a b : Nat) : unpair (npair a b) = (a, b) := by
  have h := npair_inj (npair_unpair (npair a b))
  exact Prod.ext h.1 h.2

theorem unpair_fst_le (n : Nat) : (unpair n).1 ≤ n := by
  have := le_npair_left (unpair n).1 (unpair n).2
  rwa [npair_unpair] at this

theorem unpair_snd_le (n : Nat) : (unpair n).2 ≤ n := by
  have := le_npair_right (unpair n).1 (unpair n).2
  rwa [npair_unpair] at this

theorem unpair_snd_lt (n : Nat) (h : 1 ≤ (unpair n).1) : (unpair n).2 < n := by
  have e := npair_unpair n
  obtain ⟨g, hg⟩ : ∃ g, (unpair n).1 = g + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [hg] at e
  unfold npair at e
  rw [show g + 1 + (unpair n).2 = (g + (unpair n).2) + 1 by omega] at e
  simp only [tri] at e
  omega

/-! ## Decoding types and contexts

Every number decodes to a type: numbers that code no type become `nat`. -/

def decTy (n : Nat) : Ty :=
  if _ : (unpair n).1 = 1 ∨ (unpair n).1 = 2 then
    if (unpair n).1 = 1 then
      .arrow (decTy (unpair (unpair n).2).1) (decTy (unpair (unpair n).2).2)
    else
      .prod (decTy (unpair (unpair n).2).1) (decTy (unpair (unpair n).2).2)
  else .nat
termination_by n
decreasing_by
  all_goals
    have := unpair_snd_lt n (by omega)
    have := unpair_fst_le (unpair n).2
    have := unpair_snd_le (unpair n).2
    omega

def decCtx (n : Nat) : List Ty :=
  match n with
  | 0 => []
  | n + 1 => decTy (unpair n).1 :: decCtx (unpair n).2
termination_by n
decreasing_by have := unpair_snd_le n; omega

theorem decTy_zero : decTy 0 = .nat := by
  rw [decTy]; rfl

theorem decTy_arrow (a b : Nat) : decTy (npair 1 (npair a b)) = .arrow (decTy a) (decTy b) := by
  rw [decTy]; simp [unpair_npair]

theorem decTy_prod (a b : Nat) : decTy (npair 2 (npair a b)) = .prod (decTy a) (decTy b) := by
  rw [decTy]; simp [unpair_npair]

theorem decCtx_zero : decCtx 0 = [] := by
  rw [decCtx]

theorem decCtx_succ (a g : Nat) : decCtx (npair a g + 1) = decTy a :: decCtx g := by
  rw [decCtx]; simp [unpair_npair]

/-! ## Soundness of `Typed` -/

/-- The meaning of a typing or lookup fact, under decoding. -/
def GoodTy (x : Nat) : Prop :=
  (∀ G a A, x = tyF G a A → ∃ t, a = code t ∧ HasType (decCtx G) t (decTy A)) ∧
  (∀ G k A, x = lkF G k A → ∃ h : k < (decCtx G).length, (decCtx G)[k] = decTy A)

section
attribute [local simp] tyF lkF npair_eq_iff

theorem good_ty {G a A : Nat} (h : ∃ t, a = code t ∧ HasType (decCtx G) t (decTy A)) :
    GoodTy (tyF G a A) :=
  ⟨fun _ _ _ e => by simp at e; obtain ⟨rfl, rfl, rfl⟩ := e; exact h,
   fun _ _ _ e => by simp at e⟩

theorem good_lk {G k A : Nat} (h : ∃ h : k < (decCtx G).length, (decCtx G)[k] = decTy A) :
    GoodTy (lkF G k A) :=
  ⟨fun _ _ _ e => by simp at e,
   fun _ _ _ e => by simp at e; obtain ⟨rfl, rfl, rfl⟩ := e; exact h⟩

end

theorem GoodTy.ty {G a A : Nat} (h : GoodTy (tyF G a A)) :
    ∃ t, a = code t ∧ HasType (decCtx G) t (decTy A) := h.1 _ _ _ rfl
theorem GoodTy.lk {G k A : Nat} (h : GoodTy (lkF G k A)) :
    ∃ h : k < (decCtx G).length, (decCtx G)[k] = decTy A := h.2 _ _ _ rfl

theorem goodTy_step {E : Nat → Prop} {x : Nat} (hE : ∀ y, E y → GoodTy y) (h : RTy E x) :
    GoodTy x := by
  rcases h with ⟨A, G, rfl⟩ | ⟨A, B, G, k, rfl, h₁⟩ | ⟨G, m, A, rfl, h₁⟩ |
    ⟨G, a, b, A, B, rfl, h₁, h₂⟩ | ⟨G, a, A, B, rfl, h₁⟩ | ⟨G, rfl⟩ | ⟨G, a, rfl, h₁⟩ |
    ⟨G, z, f, a, A, rfl, h₁, h₂, h₃⟩ | ⟨G, a, b, A, B, rfl, h₁, h₂⟩ | ⟨G, a, A, B, rfl, h₁⟩ |
    ⟨G, a, A, B, rfl, h₁⟩
  -- lookup
  · refine good_lk ?_
    simp only [decCtx_succ]
    exact ⟨by simp, rfl⟩
  · obtain ⟨hk, he⟩ := (hE _ h₁).lk
    refine good_lk ?_
    simp only [decCtx_succ]
    exact ⟨by simp; omega, by simpa using he⟩
  -- var
  · obtain ⟨hk, he⟩ := (hE _ h₁).lk
    exact good_ty ⟨var m, rfl, by rw [← he]; exact HasType.var hk⟩
  -- app
  · obtain ⟨t₁, rfl, ht₁⟩ := (hE _ h₁).ty
    obtain ⟨t₂, rfl, ht₂⟩ := (hE _ h₂).ty
    rw [decTy_arrow] at ht₁
    exact good_ty ⟨app t₁ t₂, rfl, .app ht₁ ht₂⟩
  -- lam
  · obtain ⟨t, rfl, ht⟩ := (hE _ h₁).ty
    rw [decCtx_succ] at ht
    exact good_ty ⟨lam t, rfl, by rw [decTy_arrow]; exact .lam ht⟩
  -- zero
  · exact good_ty ⟨.zero, rfl, by rw [decTy_zero]; exact .zero⟩
  -- succ
  · obtain ⟨t, rfl, ht⟩ := (hE _ h₁).ty
    rw [decTy_zero] at ht
    exact good_ty ⟨succ t, rfl, by rw [decTy_zero]; exact .succ ht⟩
  -- rect
  · obtain ⟨tz, rfl, hz⟩ := (hE _ h₁).ty
    obtain ⟨tf, rfl, hf⟩ := (hE _ h₂).ty
    obtain ⟨ta, rfl, ha⟩ := (hE _ h₃).ty
    rw [decTy_arrow, decTy_arrow, decTy_zero] at hf
    rw [decTy_zero] at ha
    exact good_ty ⟨rect tz tf ta, rfl, .rect hz hf ha⟩
  -- pair
  · obtain ⟨t₁, rfl, ht₁⟩ := (hE _ h₁).ty
    obtain ⟨t₂, rfl, ht₂⟩ := (hE _ h₂).ty
    exact good_ty ⟨pair t₁ t₂, rfl, by rw [decTy_prod]; exact .pair ht₁ ht₂⟩
  -- fst, snd
  · obtain ⟨t, rfl, ht⟩ := (hE _ h₁).ty
    rw [decTy_prod] at ht
    exact good_ty ⟨fst t, rfl, .fst ht⟩
  · obtain ⟨t, rfl, ht⟩ := (hE _ h₁).ty
    rw [decTy_prod] at ht
    exact good_ty ⟨snd t, rfl, .snd ht⟩

/-- Induction over a derivation table. -/
theorem DerSem.inv {R : (Nat → Prop) → Nat → Prop} {P : Nat → Prop}
    (hstep : ∀ E x, (∀ y, E y → P y) → R E x → P x) {f : Nat} (h : DerSem R f) : P f := by
  obtain ⟨s, t, len, ⟨i, hi, rfl⟩, hall⟩ := h
  have key : ∀ N, ∀ i < N, i < len → P (beta s t i) := by
    intro N
    induction N with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ N ih =>
      intro i hi hl
      refine hstep (Below s t i) _ ?_ (hall i hl)
      rintro y ⟨j, hj, rfl⟩
      exact ih j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hi)) (Nat.lt_trans hj hl)
  exact key (i + 1) i (Nat.lt_succ_self i) hi

/-- **Soundness of `Typed`**. -/
theorem typed_sound {e : Nat → Nat} (h : sat e Typed) : ∃ t, e 1 = code t ∧ HasType [] t .nat := by
  rw [sat_Typed] at h
  obtain ⟨t, hc, ht⟩ := (h.inv (P := GoodTy) fun _ _ => goodTy_step).ty
  rw [decCtx_zero, decTy_zero] at ht
  exact ⟨t, hc, ht⟩

/-! ## Building tables -/

/-- `x` occurs in some valid list. -/
def Der (R : (Nat → Prop) → Nat → Prop) (x : Nat) : Prop := ∃ L, Valid R L ∧ x ∈ L

theorem Der.collect {R} (hR : Mono R) :
    ∀ (Ls : List Nat), (∀ a ∈ Ls, Der R a) → ∃ L, Valid R L ∧ ∀ a ∈ Ls, a ∈ L
  | [], _ => ⟨[], Valid.nil, by simp⟩
  | a :: Ls, h => by
    obtain ⟨L₁, h₁, m₁⟩ := h a (by simp)
    obtain ⟨L₂, h₂, m₂⟩ := Der.collect hR Ls (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨L₁ ++ L₂, Valid.append hR h₁ h₂, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact List.mem_append_left _ m₁
    · exact List.mem_append_right _ (m₂ b hb)

theorem Der.step {R} (hR : Mono R) (Ls : List Nat) (h : ∀ a ∈ Ls, Der R a) {x : Nat}
    (hx : R (· ∈ Ls) x) : Der R x := by
  obtain ⟨L, hL, hm⟩ := Der.collect hR Ls h
  exact ⟨_, hL.snoc (hR _ _ _ hm hx), by simp⟩

theorem Der.sem {R} (hR : Mono R) {x : Nat} (h : Der R x) : DerSem R x := by
  obtain ⟨L, hL, hm⟩ := h
  exact hL.der hR hm

/-- Monotonicity of a rule set built from `∨`, `∧`, `∃`, and atoms. -/
macro "mono_tac" hE:ident : tactic => `(tactic| repeat' (first
  | exact fun h => h
  | exact $hE _
  | apply Or.imp
  | apply And.imp
  | (apply Exists.imp; intro _)))

theorem RRed.mono : Mono RRed := by
  intro E E' x hE
  unfold RRed
  mono_tac hE

abbrev DR := Der RRed

theorem DR.ax {x : Nat} (h : RRed (fun _ => False) x) : DR x :=
  Der.step RRed.mono [] (by simp) (RRed.mono _ _ _ (fun _ h => h.elim) h)

theorem DR.one {a x : Nat} (ha : DR a) (h : RRed (· = a) x) : DR x :=
  Der.step RRed.mono [a] (by simpa using ha) (RRed.mono _ _ _ (by simp) h)

theorem DR.two {a b x : Nat} (ha : DR a) (hb : DR b) (h : RRed (fun y => y = a ∨ y = b) x) :
    DR x :=
  Der.step RRed.mono [a, b] (by simp [ha, hb]) (RRed.mono _ _ _ (by simp) h)

theorem DR.three {a b c x : Nat} (ha : DR a) (hb : DR b) (hc : DR c)
    (h : RRed (fun y => y = a ∨ y = b ∨ y = c) x) : DR x :=
  Der.step RRed.mono [a, b, c] (by simp [ha, hb, hc]) (RRed.mono _ _ _ (by simp) h)

/-! ### The reduction rules, one by one -/

section
variable {E : Nat → Prop}

theorem RRed.shVarLt {c d j : Nat} (h : j < c) : RRed E (shF c d (npair 0 j) (npair 0 j)) := by
  unfold RRed; left; exact ⟨c, d, j, rfl, h⟩
theorem RRed.shVarGe {c d m : Nat} : RRed E (shF c d (npair 0 (c + m)) (npair 0 (c + m + d))) := by
  unfold RRed; iterate 1 right
  left; exact ⟨c, d, m, rfl⟩
theorem RRed.shLam {c d a r : Nat} (h : E (shF (c + 1) d a r)) :
    RRed E (shF c d (npair 2 a) (npair 2 r)) := by
  unfold RRed; iterate 2 right
  left; exact ⟨c, d, a, r, rfl, h⟩
theorem RRed.shZero {c d : Nat} : RRed E (shF c d (npair 3 0) (npair 3 0)) := by
  unfold RRed; iterate 3 right
  left; exact ⟨c, d, rfl⟩
theorem RRed.shUn {g c d a r : Nat} (hg : g = 4 ∨ g = 7 ∨ g = 8) (h : E (shF c d a r)) :
    RRed E (shF c d (npair g a) (npair g r)) := by
  unfold RRed; iterate 4 right
  left; exact ⟨g, c, d, a, r, hg, rfl, h⟩
theorem RRed.shBin {g c d a b a' b' : Nat} (hg : g = 1 ∨ g = 6) (h₁ : E (shF c d a a'))
    (h₂ : E (shF c d b b')) :
    RRed E (shF c d (npair g (npair a b)) (npair g (npair a' b'))) := by
  unfold RRed; iterate 5 right
  left; exact ⟨g, c, d, a, b, a', b', hg, rfl, h₁, h₂⟩
theorem RRed.shRect {c d z f a z' f' a' : Nat} (h₁ : E (shF c d z z')) (h₂ : E (shF c d f f'))
    (h₃ : E (shF c d a a')) : RRed E (shF c d (rectC z f a) (rectC z' f' a')) := by
  unfold RRed; iterate 6 right
  left; exact ⟨c, d, z, f, a, z', f', a', rfl, h₁, h₂, h₃⟩
theorem RRed.sbVarLt {k u j : Nat} (h : j < k) : RRed E (sbF k (npair 0 j) u (npair 0 j)) := by
  unfold RRed; iterate 7 right
  left; exact ⟨k, u, j, rfl, h⟩
theorem RRed.sbVarEq {k u r : Nat} (h : E (shF 0 k u r)) : RRed E (sbF k (npair 0 k) u r) := by
  unfold RRed; iterate 8 right
  left; exact ⟨k, u, r, rfl, h⟩
theorem RRed.sbVarGt {k u m : Nat} : RRed E (sbF k (npair 0 (k + m + 1)) u (npair 0 (k + m))) := by
  unfold RRed; iterate 9 right
  left; exact ⟨k, u, m, rfl⟩
theorem RRed.sbLam {k a u r : Nat} (h : E (sbF (k + 1) a u r)) :
    RRed E (sbF k (npair 2 a) u (npair 2 r)) := by
  unfold RRed; iterate 10 right
  left; exact ⟨k, a, u, r, rfl, h⟩
theorem RRed.sbZero {k u : Nat} : RRed E (sbF k (npair 3 0) u (npair 3 0)) := by
  unfold RRed; iterate 11 right
  left; exact ⟨k, u, rfl⟩
theorem RRed.sbUn {g k a u r : Nat} (hg : g = 4 ∨ g = 7 ∨ g = 8) (h : E (sbF k a u r)) :
    RRed E (sbF k (npair g a) u (npair g r)) := by
  unfold RRed; iterate 12 right
  left; exact ⟨g, k, a, u, r, hg, rfl, h⟩
theorem RRed.sbBin {g k a b u a' b' : Nat} (hg : g = 1 ∨ g = 6) (h₁ : E (sbF k a u a'))
    (h₂ : E (sbF k b u b')) :
    RRed E (sbF k (npair g (npair a b)) u (npair g (npair a' b'))) := by
  unfold RRed; iterate 13 right
  left; exact ⟨g, k, a, b, u, a', b', hg, rfl, h₁, h₂⟩
theorem RRed.sbRect {k z f a u z' f' a' : Nat} (h₁ : E (sbF k z u z')) (h₂ : E (sbF k f u f'))
    (h₃ : E (sbF k a u a')) : RRed E (sbF k (rectC z f a) u (rectC z' f' a')) := by
  unfold RRed; iterate 14 right
  left; exact ⟨k, z, f, a, u, z', f', a', rfl, h₁, h₂, h₃⟩
theorem RRed.whApp {a b a' : Nat} (h : E (whF a a')) :
    RRed E (whF (npair 1 (npair a b)) (npair 1 (npair a' b))) := by
  unfold RRed; iterate 15 right
  left; exact ⟨a, b, a', rfl, h⟩
theorem RRed.whBeta {a b r : Nat} (h : E (sbF 0 a b r)) :
    RRed E (whF (npair 1 (npair (npair 2 a) b)) r) := by
  unfold RRed; iterate 16 right
  left; exact ⟨a, b, r, rfl, h⟩
theorem RRed.whRect {z f a a' : Nat} (h : E (whF a a')) :
    RRed E (whF (rectC z f a) (rectC z f a')) := by
  unfold RRed; iterate 17 right
  left; exact ⟨z, f, a, a', rfl, h⟩
theorem RRed.whUn {g a a' : Nat} (hg : g = 4 ∨ g = 7 ∨ g = 8) (h : E (whF a a')) :
    RRed E (whF (npair g a) (npair g a')) := by
  unfold RRed; iterate 18 right
  left; exact ⟨g, a, a', hg, rfl, h⟩
theorem RRed.whRectZ {z f : Nat} : RRed E (whF (rectC z f (npair 3 0)) z) := by
  unfold RRed; iterate 19 right
  left; exact ⟨z, f, rfl⟩
theorem RRed.whRectS {z f a : Nat} :
    RRed E (whF (rectC z f (npair 4 a)) (npair 1 (npair (npair 1 (npair f a)) (rectC z f a)))) := by
  unfold RRed; iterate 20 right
  left; exact ⟨z, f, a, rfl⟩
theorem RRed.whFst {a b : Nat} : RRed E (whF (npair 7 (npair 6 (npair a b))) a) := by
  unfold RRed; iterate 21 right
  left; exact ⟨a, b, rfl⟩
theorem RRed.whSnd {a b : Nat} : RRed E (whF (npair 8 (npair 6 (npair a b))) b) := by
  unfold RRed; iterate 22 right
  left; exact ⟨a, b, rfl⟩
theorem RRed.wnRefl {a : Nat} : RRed E (wnF a a) := by
  unfold RRed; iterate 23 right
  left; exact ⟨a, rfl⟩
theorem RRed.wnStep {a a' r : Nat} (h₁ : E (whF a a')) (h₂ : E (wnF a' r)) : RRed E (wnF a r) := by
  unfold RRed; iterate 24 right
  left; exact ⟨a, a', r, rfl, h₁, h₂⟩
theorem RRed.numZ : RRed E (numF (npair 3 0) 0) := by
  unfold RRed; iterate 25 right
  left; rfl
theorem RRed.numS {y m : Nat} (h : E (numF y m)) : RRed E (numF (npair 4 y) (m + 1)) := by
  unfold RRed; iterate 26 right
  exact ⟨y, m, rfl, h⟩

end

/-! ### Shifting and substitution -/

theorem sh_complete : ∀ (t : Term) (c d : Nat),
    DR (shF c d (code t) (code (psubst (upN c (shiftBy d)) t)))
  | var j, c, d => by
    rcases Nat.lt_or_ge j c with h | h
    · show DR (shF c d (npair 0 j) (code (upN c (shiftBy d) j)))
      rw [upN_lt h]
      exact DR.ax (RRed.shVarLt h)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      show DR (shF c d (npair 0 (c + m)) (code (upN c (shiftBy d) (c + m))))
      rw [upN_ge]
      show DR (shF c d (npair 0 (c + m)) (npair 0 (m + d + c)))
      rw [show m + d + c = c + m + d by omega]
      exact DR.ax RRed.shVarGe
  | app a b, c, d => by
    show DR (shF c d (npair 1 (npair (code a) (code b)))
      (npair 1 (npair (code (psubst (upN c (shiftBy d)) a)) (code (psubst (upN c (shiftBy d)) b)))))
    exact DR.two (sh_complete a c d) (sh_complete b c d) (RRed.shBin (.inl rfl) (.inl rfl) (.inr rfl))
  | lam a, c, d => by
    show DR (shF c d (npair 2 (code a)) (npair 2 (code (psubst (upN (c + 1) (shiftBy d)) a))))
    exact DR.one (sh_complete a (c + 1) d) (RRed.shLam rfl)
  | zero, c, d => DR.ax RRed.shZero
  | succ a, c, d => by
    show DR (shF c d (npair 4 (code a)) (npair 4 (code (psubst (upN c (shiftBy d)) a))))
    exact DR.one (sh_complete a c d) (RRed.shUn (.inl rfl) rfl)
  | rect z f a, c, d => by
    show DR (shF c d (rectC (code z) (code f) (code a))
      (rectC (code (psubst (upN c (shiftBy d)) z)) (code (psubst (upN c (shiftBy d)) f))
        (code (psubst (upN c (shiftBy d)) a))))
    exact DR.three (sh_complete z c d) (sh_complete f c d) (sh_complete a c d)
      (RRed.shRect (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)))
  | pair a b, c, d => by
    show DR (shF c d (npair 6 (npair (code a) (code b)))
      (npair 6 (npair (code (psubst (upN c (shiftBy d)) a)) (code (psubst (upN c (shiftBy d)) b)))))
    exact DR.two (sh_complete a c d) (sh_complete b c d) (RRed.shBin (.inr rfl) (.inl rfl) (.inr rfl))
  | fst a, c, d => by
    show DR (shF c d (npair 7 (code a)) (npair 7 (code (psubst (upN c (shiftBy d)) a))))
    exact DR.one (sh_complete a c d) (RRed.shUn (.inr (.inl rfl)) rfl)
  | snd a, c, d => by
    show DR (shF c d (npair 8 (code a)) (npair 8 (code (psubst (upN c (shiftBy d)) a))))
    exact DR.one (sh_complete a c d) (RRed.shUn (.inr (.inr rfl)) rfl)

theorem sb_complete : ∀ (t : Term) (k : Nat) (u : Term),
    DR (sbF k (code t) (code u) (code (psubst (upN k (scons u var)) t)))
  | var j, k, u => by
    rcases Nat.lt_trichotomy j k with h | rfl | h
    · show DR (sbF k (npair 0 j) (code u) (code (upN k (scons u var) j)))
      rw [upN_lt h]
      exact DR.ax (RRed.sbVarLt h)
    · show DR (sbF j (npair 0 j) (code u) (code (upN j (scons u var) (j + 0))))
      rw [upN_ge]
      show DR (sbF j (npair 0 j) (code u) (code (psubst (upN 0 (shiftBy j)) u)))
      exact DR.one (sh_complete u 0 j) (RRed.sbVarEq rfl)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
      show DR (sbF k (npair 0 (k + m + 1)) (code u) (code (upN k (scons u var) (k + (m + 1)))))
      rw [upN_ge]
      show DR (sbF k (npair 0 (k + m + 1)) (code u) (npair 0 (m + k)))
      rw [Nat.add_comm m k]
      exact DR.ax RRed.sbVarGt
  | app a b, k, u => by
    show DR (sbF k (npair 1 (npair (code a) (code b))) (code u)
      (npair 1 (npair (code (psubst (upN k (scons u var)) a)) (code (psubst (upN k (scons u var)) b)))))
    exact DR.two (sb_complete a k u) (sb_complete b k u) (RRed.sbBin (.inl rfl) (.inl rfl) (.inr rfl))
  | lam a, k, u => by
    show DR (sbF k (npair 2 (code a)) (code u) (npair 2 (code (psubst (upN (k + 1) (scons u var)) a))))
    exact DR.one (sb_complete a (k + 1) u) (RRed.sbLam rfl)
  | zero, k, u => DR.ax RRed.sbZero
  | succ a, k, u => by
    show DR (sbF k (npair 4 (code a)) (code u) (npair 4 (code (psubst (upN k (scons u var)) a))))
    exact DR.one (sb_complete a k u) (RRed.sbUn (.inl rfl) rfl)
  | rect z f a, k, u => by
    show DR (sbF k (rectC (code z) (code f) (code a)) (code u)
      (rectC (code (psubst (upN k (scons u var)) z)) (code (psubst (upN k (scons u var)) f))
        (code (psubst (upN k (scons u var)) a))))
    exact DR.three (sb_complete z k u) (sb_complete f k u) (sb_complete a k u)
      (RRed.sbRect (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)))
  | pair a b, k, u => by
    show DR (sbF k (npair 6 (npair (code a) (code b))) (code u)
      (npair 6 (npair (code (psubst (upN k (scons u var)) a)) (code (psubst (upN k (scons u var)) b)))))
    exact DR.two (sb_complete a k u) (sb_complete b k u) (RRed.sbBin (.inr rfl) (.inl rfl) (.inr rfl))
  | fst a, k, u => by
    show DR (sbF k (npair 7 (code a)) (code u) (npair 7 (code (psubst (upN k (scons u var)) a))))
    exact DR.one (sb_complete a k u) (RRed.sbUn (.inr (.inl rfl)) rfl)
  | snd a, k, u => by
    show DR (sbF k (npair 8 (code a)) (code u) (npair 8 (code (psubst (upN k (scons u var)) a))))
    exact DR.one (sb_complete a k u) (RRed.sbUn (.inr (.inr rfl)) rfl)

/-! ### Reduction and numerals -/

theorem wh_complete {t t' : Term} (h : WHRed t t') : DR (whF (code t) (code t')) := by
  induction h with
  | @appNe a a' b _ ih =>
    show DR (whF (npair 1 (npair (code a) (code b))) (npair 1 (npair (code a') (code b))))
    exact DR.one ih (RRed.whApp rfl)
  | @appLam a b =>
    rw [subst_single]
    show DR (whF (npair 1 (npair (npair 2 (code a)) (code b)))
      (code (psubst (upN 0 (scons b var)) a)))
    exact DR.one (sb_complete a 0 b) (RRed.whBeta rfl)
  | @rectNe a a' z f _ ih =>
    show DR (whF (rectC (code z) (code f) (code a)) (rectC (code z) (code f) (code a')))
    exact DR.one ih (RRed.whRect rfl)
  | @succ a a' _ ih =>
    show DR (whF (npair 4 (code a)) (npair 4 (code a')))
    exact DR.one ih (RRed.whUn (.inl rfl) rfl)
  | @rectz z f =>
    show DR (whF (rectC (code z) (code f) (npair 3 0)) (code z))
    exact DR.ax RRed.whRectZ
  | @rects z f a =>
    show DR (whF (rectC (code z) (code f) (npair 4 (code a)))
      (npair 1 (npair (npair 1 (npair (code f) (code a))) (rectC (code z) (code f) (code a)))))
    exact DR.ax RRed.whRectS
  | @fstNe a a' _ ih =>
    show DR (whF (npair 7 (code a)) (npair 7 (code a')))
    exact DR.one ih (RRed.whUn (.inr (.inl rfl)) rfl)
  | @sndNe a a' _ ih =>
    show DR (whF (npair 8 (code a)) (npair 8 (code a')))
    exact DR.one ih (RRed.whUn (.inr (.inr rfl)) rfl)
  | @fstPair a b =>
    show DR (whF (npair 7 (npair 6 (npair (code a) (code b)))) (code a))
    exact DR.ax RRed.whFst
  | @sndPair a b =>
    show DR (whF (npair 8 (npair 6 (npair (code a) (code b)))) (code b))
    exact DR.ax RRed.whSnd

theorem wn_complete {t v : Term} (h : t ⇒* v) : DR (wnF (code t) (code v)) := by
  induction h with
  | refl => exact DR.ax RRed.wnRefl
  | step r _ ih => exact DR.two (wh_complete r) ih (RRed.wnStep (.inl rfl) (.inr rfl))

theorem num_complete : ∀ n, DR (numF (code (numeral n)) n)
  | 0 => DR.ax RRed.numZ
  | n + 1 => by
    show DR (numF (npair 4 (code (numeral n))) (n + 1))
    exact DR.one (num_complete n) (RRed.numS rfl)

/-- **Completeness of `Norm`**. -/
theorem norm_complete {e : Nat → Nat} {t : Term} (hc : e 1 = code t) (h : t ⇒* numeral (e 0)) :
    sat e Norm := by
  rw [sat_Norm, hc]
  exact ⟨_, (wn_complete h).sem RRed.mono, (num_complete (e 0)).sem RRed.mono⟩

/-! ## The normalization statement is true -/

/-- **`NormStmt` is true** in the standard model. Choosing the witness `n`
before knowing whether `c` is well typed uses excluded middle. -/
theorem normStmt_true (e : Nat → Nat) : sat e NormStmt := by
  simp only [NormStmt, sat_all, sat_ex, sat_imp]
  intro c
  rcases Classical.em (∃ t, c = code t ∧ HasType [] t .nat) with ⟨t, rfl, ht⟩ | hn
  · obtain ⟨m, hm⟩ := normalize ht
    exact ⟨m, fun _ => norm_complete rfl hm⟩
  · exact ⟨0, fun h => (hn (typed_sound h)).elim⟩

/-- **`NormStmt` is true but not provable in HA.** -/
theorem normStmt_independent : (∀ e, sat e NormStmt) ∧ ¬ HA.Proves [] NormStmt :=
  ⟨normStmt_true, HA_not_proves_normalization⟩

end Rz
