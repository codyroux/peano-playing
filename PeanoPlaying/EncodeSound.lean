import PeanoPlaying.Encode

/-!
# Soundness of the reduction encoding

`norm_sound`: if `Norm(⌜t⌝, m)` is true, then `t ⇒* numeral m`. Each fact of
a derivation table for `JustRed` is decoded, by induction on its index, into
an actual shifting, substitution, reduction or numeral (`Good`).
-/

namespace Rz

open Term

/-! ## Decoding terms -/

section
attribute [local simp] npair_eq_iff

theorem code_var_inv {T : Term} {j : Nat} (h : code T = npair 0 j) : T = var j := by
  cases T <;> simp_all [code]

theorem code_app_inv {T : Term} {a b : Nat} (h : code T = npair 1 (npair a b)) :
    ∃ A B, T = app A B ∧ code A = a ∧ code B = b := by
  cases T <;> simp [code] at h <;> exact ⟨_, _, rfl, h.1, h.2⟩

theorem code_lam_inv {T : Term} {a : Nat} (h : code T = npair 2 a) :
    ∃ A, T = lam A ∧ code A = a := by
  cases T <;> simp_all [code]

theorem code_zero_inv {T : Term} (h : code T = npair 3 0) : T = zero := by
  cases T <;> simp_all [code]

theorem code_succ_inv {T : Term} {a : Nat} (h : code T = npair 4 a) :
    ∃ A, T = succ A ∧ code A = a := by
  cases T <;> simp_all [code]

theorem code_rect_inv {T : Term} {z f a : Nat} (h : code T = rectC z f a) :
    ∃ Z F A, T = rect Z F A ∧ code Z = z ∧ code F = f ∧ code A = a := by
  cases T <;> simp [code, rectC] at h <;> exact ⟨_, _, _, rfl, h.1, h.2.1, h.2.2⟩

theorem code_pair_inv {T : Term} {a b : Nat} (h : code T = npair 6 (npair a b)) :
    ∃ A B, T = pair A B ∧ code A = a ∧ code B = b := by
  cases T <;> simp [code] at h <;> exact ⟨_, _, rfl, h.1, h.2⟩

theorem code_fst_inv {T : Term} {a : Nat} (h : code T = npair 7 a) :
    ∃ A, T = fst A ∧ code A = a := by
  cases T <;> simp_all [code]

theorem code_snd_inv {T : Term} {a : Nat} (h : code T = npair 8 a) :
    ∃ A, T = snd A ∧ code A = a := by
  cases T <;> simp_all [code]

end

/-! ## Iterated lifting -/

def upN : Nat → (Nat → Term) → Nat → Term
  | 0, σ => σ
  | k + 1, σ => up (upN k σ)

def shiftBy (d : Nat) : Nat → Term := fun i => var (i + d)

theorem upN_lt {σ : Nat → Term} : ∀ {k j : Nat}, j < k → upN k σ j = var j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, 0, _ => rfl
  | k + 1, j + 1, h => by
    show sh (upN k σ j) = _
    rw [upN_lt (by omega)]; rfl

theorem upN_ge {σ : Nat → Term} : ∀ (k j : Nat), upN k σ (k + j) = psubst (shiftBy k) (σ j)
  | 0, j => by
    show σ (0 + j) = _
    rw [Nat.zero_add]
    have : shiftBy 0 = var := by funext i; rfl
    rw [this, psubst_var]
  | k + 1, j => by
    rw [show k + 1 + j = (k + j) + 1 by omega]
    show up (upN k σ) ((k + j) + 1) = _
    rw [up_succ, upN_ge k j, sh_eq, psubst_psubst]
    rfl

/-! ## Meaning of the facts -/

def ShM (c d a r : Nat) : Prop := ∀ T, code T = a → r = code (psubst (upN c (shiftBy d)) T)
def SbM (k a u r : Nat) : Prop :=
  ∀ T U, code T = a → code U = u → r = code (psubst (upN k (scons U var)) T)
def WhM (a r : Nat) : Prop := ∀ T, code T = a → ∃ R, code R = r ∧ WHRed T R
def WnM (a r : Nat) : Prop := ∀ T, code T = a → ∃ R, code R = r ∧ T ⇒* R
def NumM (y m : Nat) : Prop := y = code (numeral m)

def Good (x : Nat) : Prop :=
  (∀ c d a r, x = shF c d a r → ShM c d a r) ∧
  (∀ k a u r, x = sbF k a u r → SbM k a u r) ∧
  (∀ a r, x = whF a r → WhM a r) ∧
  (∀ a r, x = wnF a r → WnM a r) ∧
  (∀ y m, x = numF y m → NumM y m)

section
attribute [local simp] shF sbF whF wnF numF npair_eq_iff

theorem good_sh {c d a r : Nat} (h : ShM c d a r) : Good (shF c d a r) :=
  ⟨fun _ _ _ _ e => by simp at e; obtain ⟨rfl, rfl, rfl, rfl⟩ := e; exact h,
   fun _ _ _ _ e => by simp at e, fun _ _ e => by simp at e, fun _ _ e => by simp at e,
   fun _ _ e => by simp at e⟩

theorem good_sb {k a u r : Nat} (h : SbM k a u r) : Good (sbF k a u r) :=
  ⟨fun _ _ _ _ e => by simp at e,
   fun _ _ _ _ e => by simp at e; obtain ⟨rfl, rfl, rfl, rfl⟩ := e; exact h,
   fun _ _ e => by simp at e, fun _ _ e => by simp at e, fun _ _ e => by simp at e⟩

theorem good_wh {a r : Nat} (h : WhM a r) : Good (whF a r) :=
  ⟨fun _ _ _ _ e => by simp at e, fun _ _ _ _ e => by simp at e,
   fun _ _ e => by simp at e; obtain ⟨rfl, rfl⟩ := e; exact h,
   fun _ _ e => by simp at e, fun _ _ e => by simp at e⟩

theorem good_wn {a r : Nat} (h : WnM a r) : Good (wnF a r) :=
  ⟨fun _ _ _ _ e => by simp at e, fun _ _ _ _ e => by simp at e, fun _ _ e => by simp at e,
   fun _ _ e => by simp at e; obtain ⟨rfl, rfl⟩ := e; exact h,
   fun _ _ e => by simp at e⟩

theorem good_num {y m : Nat} (h : NumM y m) : Good (numF y m) :=
  ⟨fun _ _ _ _ e => by simp at e, fun _ _ _ _ e => by simp at e, fun _ _ e => by simp at e,
   fun _ _ e => by simp at e,
   fun _ _ e => by simp at e; obtain ⟨rfl, rfl⟩ := e; exact h⟩

end

theorem Good.sh {c d a r : Nat} (h : Good (shF c d a r)) : ShM c d a r := h.1 _ _ _ _ rfl
theorem Good.sb {k a u r : Nat} (h : Good (sbF k a u r)) : SbM k a u r := h.2.1 _ _ _ _ rfl
theorem Good.wh {a r : Nat} (h : Good (whF a r)) : WhM a r := h.2.2.1 _ _ rfl
theorem Good.wn {a r : Nat} (h : Good (wnF a r)) : WnM a r := h.2.2.2.1 _ _ rfl
theorem Good.num {y m : Nat} (h : Good (numF y m)) : NumM y m := h.2.2.2.2 _ _ rfl

/-! ## Every rule preserves `Good` -/

theorem good_step {E : Nat → Prop} {x : Nat} (hE : ∀ y, E y → Good y) (h : RRed E x) : Good x := by
  rcases h with
    ⟨c, d, j, rfl, hj⟩ | ⟨c, d, m, rfl⟩ | ⟨c, d, a, r, rfl, h₁⟩ | ⟨c, d, rfl⟩ |
    ⟨g, c, d, a, r, hg, rfl, h₁⟩ | ⟨g, c, d, a, b, a', b', hg, rfl, h₁, h₂⟩ |
    ⟨c, d, z, f, a, z', f', a', rfl, h₁, h₂, h₃⟩ |
    ⟨k, u, j, rfl, hj⟩ | ⟨k, u, r, rfl, h₁⟩ | ⟨k, u, m, rfl⟩ | ⟨k, a, u, r, rfl, h₁⟩ | ⟨k, u, rfl⟩ |
    ⟨g, k, a, u, r, hg, rfl, h₁⟩ | ⟨g, k, a, b, u, a', b', hg, rfl, h₁, h₂⟩ |
    ⟨k, z, f, a, u, z', f', a', rfl, h₁, h₂, h₃⟩ |
    ⟨a, b, a', rfl, h₁⟩ | ⟨a, b, r, rfl, h₁⟩ | ⟨z, f, a, a', rfl, h₁⟩ | ⟨g, a, a', hg, rfl, h₁⟩ |
    ⟨z, f, rfl⟩ | ⟨z, f, a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ |
    ⟨a, rfl⟩ | ⟨a, a', r, rfl, h₁, h₂⟩ |
    rfl | ⟨y, m, rfl, h₁⟩
  -- shifting
  · exact good_sh fun T hT => by
      rw [code_var_inv hT]; show npair 0 j = code (upN c (shiftBy d) j); rw [upN_lt hj]; rfl
  · refine good_sh fun T hT => ?_
    rw [code_var_inv hT]
    show _ = code (upN c (shiftBy d) (c + m))
    rw [upN_ge]
    show npair 0 (c + m + d) = npair 0 (m + d + c)
    congr 1; omega
  · have ih := (hE _ h₁).sh
    refine good_sh fun T hT => ?_
    obtain ⟨A, rfl, rfl⟩ := code_lam_inv hT
    show npair 2 r = npair 2 _
    rw [ih A rfl]; rfl
  · exact good_sh fun T hT => by rw [code_zero_inv hT]; rfl
  · have ih := (hE _ h₁).sh
    refine good_sh fun T hT => ?_
    rcases hg with rfl | rfl | rfl
    · obtain ⟨A, rfl, rfl⟩ := code_succ_inv hT
      show npair 4 r = npair 4 _; rw [ih A rfl]
    · obtain ⟨A, rfl, rfl⟩ := code_fst_inv hT
      show npair 7 r = npair 7 _; rw [ih A rfl]
    · obtain ⟨A, rfl, rfl⟩ := code_snd_inv hT
      show npair 8 r = npair 8 _; rw [ih A rfl]
  · have ih₁ := (hE _ h₁).sh
    have ih₂ := (hE _ h₂).sh
    refine good_sh fun T hT => ?_
    rcases hg with rfl | rfl
    · obtain ⟨A, B, rfl, rfl, rfl⟩ := code_app_inv hT
      show npair 1 (npair a' b') = npair 1 (npair _ _); rw [ih₁ A rfl, ih₂ B rfl]
    · obtain ⟨A, B, rfl, rfl, rfl⟩ := code_pair_inv hT
      show npair 6 (npair a' b') = npair 6 (npair _ _); rw [ih₁ A rfl, ih₂ B rfl]
  · have ih₁ := (hE _ h₁).sh
    have ih₂ := (hE _ h₂).sh
    have ih₃ := (hE _ h₃).sh
    refine good_sh fun T hT => ?_
    obtain ⟨Z, F, A, rfl, rfl, rfl, rfl⟩ := code_rect_inv hT
    show rectC z' f' a' = rectC _ _ _; rw [ih₁ Z rfl, ih₂ F rfl, ih₃ A rfl]
  -- substitution
  · exact good_sb fun T U hT _ => by
      rw [code_var_inv hT]; show npair 0 j = code (upN k (scons U var) j); rw [upN_lt hj]; rfl
  · have ih := (hE _ h₁).sh
    refine good_sb fun T U hT hU => ?_
    rw [code_var_inv hT, ih U hU]
    show _ = code (upN k (scons U var) (k + 0))
    rw [upN_ge]; rfl
  · refine good_sb fun T U hT _ => ?_
    rw [code_var_inv hT]
    show _ = code (upN k (scons U var) (k + (m + 1)))
    rw [upN_ge]
    show npair 0 (k + m) = npair 0 (m + k)
    congr 1; omega
  · have ih := (hE _ h₁).sb
    refine good_sb fun T U hT hU => ?_
    obtain ⟨A, rfl, rfl⟩ := code_lam_inv hT
    show npair 2 r = npair 2 _
    rw [ih A U rfl hU]; rfl
  · exact good_sb fun T _ hT _ => by rw [code_zero_inv hT]; rfl
  · have ih := (hE _ h₁).sb
    refine good_sb fun T U hT hU => ?_
    rcases hg with rfl | rfl | rfl
    · obtain ⟨A, rfl, rfl⟩ := code_succ_inv hT
      show npair 4 r = npair 4 _; rw [ih A U rfl hU]
    · obtain ⟨A, rfl, rfl⟩ := code_fst_inv hT
      show npair 7 r = npair 7 _; rw [ih A U rfl hU]
    · obtain ⟨A, rfl, rfl⟩ := code_snd_inv hT
      show npair 8 r = npair 8 _; rw [ih A U rfl hU]
  · have ih₁ := (hE _ h₁).sb
    have ih₂ := (hE _ h₂).sb
    refine good_sb fun T U hT hU => ?_
    rcases hg with rfl | rfl
    · obtain ⟨A, B, rfl, rfl, rfl⟩ := code_app_inv hT
      show npair 1 (npair a' b') = npair 1 (npair _ _); rw [ih₁ A U rfl hU, ih₂ B U rfl hU]
    · obtain ⟨A, B, rfl, rfl, rfl⟩ := code_pair_inv hT
      show npair 6 (npair a' b') = npair 6 (npair _ _); rw [ih₁ A U rfl hU, ih₂ B U rfl hU]
  · have ih₁ := (hE _ h₁).sb
    have ih₂ := (hE _ h₂).sb
    have ih₃ := (hE _ h₃).sb
    refine good_sb fun T U hT hU => ?_
    obtain ⟨Z, F, A, rfl, rfl, rfl, rfl⟩ := code_rect_inv hT
    show rectC z' f' a' = rectC _ _ _; rw [ih₁ Z U rfl hU, ih₂ F U rfl hU, ih₃ A U rfl hU]
  -- weak head reduction
  · have ih := (hE _ h₁).wh
    refine good_wh fun T hT => ?_
    obtain ⟨A, B, rfl, rfl, rfl⟩ := code_app_inv hT
    obtain ⟨R, rfl, hR⟩ := ih A rfl
    exact ⟨app R B, rfl, .appNe hR⟩
  · have ih := (hE _ h₁).sb
    refine good_wh fun T hT => ?_
    obtain ⟨L, B, rfl, hL, rfl⟩ := code_app_inv hT
    obtain ⟨A, rfl, rfl⟩ := code_lam_inv hL
    refine ⟨_, (ih A B rfl rfl).symm, ?_⟩
    have := WHRed.appLam (t := A) (u := B)
    rw [subst_single] at this
    exact this
  · have ih := (hE _ h₁).wh
    refine good_wh fun T hT => ?_
    obtain ⟨Z, F, A, rfl, rfl, rfl, rfl⟩ := code_rect_inv hT
    obtain ⟨R, rfl, hR⟩ := ih A rfl
    exact ⟨rect Z F R, rfl, .rectNe hR⟩
  · have ih := (hE _ h₁).wh
    refine good_wh fun T hT => ?_
    rcases hg with rfl | rfl | rfl
    · obtain ⟨A, rfl, rfl⟩ := code_succ_inv hT
      obtain ⟨R, rfl, hR⟩ := ih A rfl
      exact ⟨succ R, rfl, .succ hR⟩
    · obtain ⟨A, rfl, rfl⟩ := code_fst_inv hT
      obtain ⟨R, rfl, hR⟩ := ih A rfl
      exact ⟨fst R, rfl, .fstNe hR⟩
    · obtain ⟨A, rfl, rfl⟩ := code_snd_inv hT
      obtain ⟨R, rfl, hR⟩ := ih A rfl
      exact ⟨snd R, rfl, .sndNe hR⟩
  · refine good_wh fun T hT => ?_
    obtain ⟨Z, F, A, rfl, rfl, rfl, hA⟩ := code_rect_inv hT
    rw [code_zero_inv hA]
    exact ⟨Z, rfl, .rectz⟩
  · refine good_wh fun T hT => ?_
    obtain ⟨Z, F, S, rfl, rfl, rfl, hS⟩ := code_rect_inv hT
    obtain ⟨A, rfl, rfl⟩ := code_succ_inv hS
    exact ⟨app (app F A) (rect Z F A), rfl, .rects⟩
  · refine good_wh fun T hT => ?_
    obtain ⟨P, rfl, hP⟩ := code_fst_inv hT
    obtain ⟨A, B, rfl, rfl, rfl⟩ := code_pair_inv hP
    exact ⟨A, rfl, .fstPair⟩
  · refine good_wh fun T hT => ?_
    obtain ⟨P, rfl, hP⟩ := code_snd_inv hT
    obtain ⟨A, B, rfl, rfl, rfl⟩ := code_pair_inv hP
    exact ⟨B, rfl, .sndPair⟩
  -- weak head normalization
  · exact good_wn fun T hT => ⟨T, hT, .refl⟩
  · have ih₁ := (hE _ h₁).wh
    have ih₂ := (hE _ h₂).wn
    refine good_wn fun T hT => ?_
    obtain ⟨R₁, hR₁, h₁⟩ := ih₁ T hT
    obtain ⟨R, hR, h₂⟩ := ih₂ R₁ hR₁
    exact ⟨R, hR, .step h₁ h₂⟩
  -- numerals
  · exact good_num rfl
  · have ih := (hE _ h₁).num
    exact good_num (by rw [NumM, ih]; rfl)

/-! ## Tables -/

theorem DerSem.good {f : Nat} (h : DerSem RRed f) : Good f := by
  obtain ⟨s, t, len, ⟨i, hi, rfl⟩, hall⟩ := h
  have key : ∀ N, ∀ i < N, i < len → Good (beta s t i) := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi hl
      refine good_step (E := Below s t i) ?_ (hall i hl)
      rintro y ⟨j, hj, rfl⟩
      exact ih j (by omega) (by omega)
  exact key (i + 1) i (by omega) hi

/-- **Soundness of `Norm`**. -/
theorem norm_sound {t : Term} {m : Nat} (h : sat (scons m (scons (code t) (fun _ => 0))) Norm) :
    t ⇒* numeral m := by
  rw [sat_Norm] at h
  obtain ⟨y, h₁, h₂⟩ := h
  obtain ⟨R, hR, hred⟩ := h₁.good.wn t rfl
  have hy : y = code (numeral m) := h₂.good.num
  rw [hy] at hR
  rw [code_inj hR] at hred
  exact hred

end Rz
