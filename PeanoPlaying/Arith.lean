import PeanoPlaying.Prelim

/-!
# Arithmetic semantics and a small formula DSL

* `sat e φ`: Tarski truth of an HA formula in the standard model, with
  variable `k` read as `e k`.
* A higher-order DSL for writing HA formulas with named binders. A DSL
  formula is a function of the binder depth; `lv l` is the variable bound at
  level `l`, which at depth `d` is the de Bruijn index `d - l - 1`. Formulas
  are always produced at a concrete depth, so `simp` computes their truth
  conditions.
* The Cantor pairing relation `z = npair a b` as an HA equation.
* Gödel's β-function `s mod (1 + (i+1) t)`, and the Chinese remainder
  argument that every finite list is coded by a β-pair `(s, t)`.
-/

namespace Rz

open HA

/-! ## Truth in the standard model -/

def sat : (Nat → Nat) → HA.Formula → Prop
  | e, .eq a b => eval e a = eval e b
  | _, .bot => False
  | e, .and φ ψ => sat e φ ∧ sat e ψ
  | e, .or φ ψ => sat e φ ∨ sat e ψ
  | e, .imp φ ψ => sat e φ → sat e ψ
  | e, .ex φ => ∃ n, sat (scons n e) φ
  | e, .all φ => ∀ n, sat (scons n e) φ

@[simp] theorem sat_eq (e : Nat → Nat) (a b : HA.Tm) :
    sat e (.eq a b) ↔ eval e a = eval e b := Iff.rfl
@[simp] theorem sat_bot (e : Nat → Nat) : sat e .bot ↔ False := Iff.rfl
@[simp] theorem sat_and (e : Nat → Nat) (φ ψ : HA.Formula) :
    sat e (.and φ ψ) ↔ sat e φ ∧ sat e ψ := Iff.rfl
@[simp] theorem sat_or (e : Nat → Nat) (φ ψ : HA.Formula) :
    sat e (.or φ ψ) ↔ sat e φ ∨ sat e ψ := Iff.rfl
@[simp] theorem sat_imp (e : Nat → Nat) (φ ψ : HA.Formula) :
    sat e (.imp φ ψ) ↔ (sat e φ → sat e ψ) := Iff.rfl
@[simp] theorem sat_ex (e : Nat → Nat) (φ : HA.Formula) :
    sat e (.ex φ) ↔ ∃ n, sat (scons n e) φ := Iff.rfl
@[simp] theorem sat_all (e : Nat → Nat) (φ : HA.Formula) :
    sat e (.all φ) ↔ ∀ n, sat (scons n e) φ := Iff.rfl

@[simp] theorem eval_var (e : Nat → Nat) (k : Nat) : eval e (.var k) = e k := rfl
@[simp] theorem eval_zero (e : Nat → Nat) : eval e .zero = 0 := rfl
@[simp] theorem eval_succ (e : Nat → Nat) (a : HA.Tm) : eval e (.succ a) = eval e a + 1 := rfl
@[simp] theorem eval_add (e : Nat → Nat) (a b : HA.Tm) :
    eval e (.add a b) = eval e a + eval e b := rfl
@[simp] theorem eval_mul (e : Nat → Nat) (a b : HA.Tm) :
    eval e (.mul a b) = eval e a * eval e b := rfl

/-! ## The DSL -/

namespace DSL

abbrev T := Nat → HA.Tm
abbrev F := Nat → HA.Formula

/-- The variable bound at level `l`. -/
def lv (l : Nat) : T := fun d => .var (d - l - 1)

@[simp] def fEx (f : T → F) : F := fun d => .ex (f (lv d) (d + 1))
@[simp] def fAll (f : T → F) : F := fun d => .all (f (lv d) (d + 1))
@[simp] def fAnd (p q : F) : F := fun d => .and (p d) (q d)
@[simp] def fOr (p q : F) : F := fun d => .or (p d) (q d)
@[simp] def fImp (p q : F) : F := fun d => .imp (p d) (q d)
@[simp] def fEq (a b : T) : F := fun d => .eq (a d) (b d)
@[simp] def fBot : F := fun _ => .bot
@[simp] def tAdd (a b : T) : T := fun d => .add (a d) (b d)
@[simp] def tMul (a b : T) : T := fun d => .mul (a d) (b d)
@[simp] def tS (a : T) : T := fun d => .succ (a d)
@[simp] def tZ : T := fun _ => .zero

/-- Literals. -/
@[simp] def tN : Nat → T
  | 0 => tZ
  | n + 1 => tS (tN n)

/-- `a < b`. -/
def fLt (a b : T) : F := fEx fun k => fEq (tAdd a (tS k)) b

/-- A bounded universal `∀ x < b. f x`, in the shape recognized by `Sig`. -/
@[simp] def fBall (b : T) (f : T → F) : F :=
  fAll fun x => fImp (fEx fun k => fEq (tAdd x (tS k)) b) (f x)

/-- A bounded existential `∃ x < b. f x`. -/
@[simp] def fBex (b : T) (f : T → F) : F :=
  fEx fun x => fAnd (fEx fun k => fEq (tAdd x (tS k)) b) (f x)

/-- Iterated conjunction and disjunction. -/
def fAnds : List F → F
  | [] => fEq tZ tZ
  | [p] => p
  | p :: ps => fAnd p (fAnds ps)

def fOrs : List F → F
  | [] => fBot
  | [p] => p
  | p :: ps => fOr p (fOrs ps)

/-- `2 z = (a+b)(a+b+1) + 2b`, i.e. `z = npair a b`. -/
def fP (a b z : T) : F :=
  fEq (tAdd z z) (tAdd (tMul (tAdd a b) (tS (tAdd a b))) (tAdd b b))

/-- `x = s mod (1 + (i+1) t)`, Gödel's β-function. -/
def fBeta (s t i x : T) : F :=
  fEx fun q => fAnd (fEq s (tAdd (tMul q (tS (tMul (tS i) t))) x))
    (fEx fun k => fEq (tAdd x (tS k)) (tS (tMul (tS i) t)))

end DSL

open DSL

@[simp] theorem eval_lv (e : Nat → Nat) (l d : Nat) : eval e (lv l d) = e (d - l - 1) := rfl

theorem sat_fAnds (e : Nat → Nat) (d : Nat) :
    ∀ ps : List F, sat e (fAnds ps d) ↔ ∀ p ∈ ps, sat e (p d)
  | [] => by simp [fAnds]
  | [p] => by simp [fAnds]
  | p :: q :: ps => by
    have := sat_fAnds e d (q :: ps)
    simp only [fAnds, fAnd, sat_and] at this ⊢
    rw [this]; simp

theorem sat_fOrs (e : Nat → Nat) (d : Nat) :
    ∀ ps : List F, sat e (fOrs ps d) ↔ ∃ p ∈ ps, sat e (p d)
  | [] => by simp [fOrs]
  | [p] => by simp [fOrs]
  | p :: q :: ps => by
    have := sat_fOrs e d (q :: ps)
    simp only [fOrs, fOr, sat_or] at this ⊢
    rw [this]; simp

/-! ## Pairing -/

theorem tri_two (n : Nat) : tri n + tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tri]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
    omega

theorem pair_iff (a b z : Nat) :
    z + z = (a + b) * (a + b + 1) + (b + b) ↔ z = npair a b := by
  have h := tri_two (a + b)
  unfold npair
  constructor
  · intro e; omega
  · intro e; omega

@[simp] theorem sat_fP (e : Nat → Nat) (d : Nat) (a b z : T) :
    sat e (fP a b z d) ↔ eval e (z d) = npair (eval e (a d)) (eval e (b d)) := by
  simp only [fP, fEq, tAdd, tMul, tS, sat_eq, eval]; exact pair_iff _ _ _

theorem exists_add_succ (a b : Nat) : (∃ k, a + (k + 1) = b) ↔ a < b :=
  ⟨fun h => h.elim fun k hk => hk ▸ Nat.lt_add_of_pos_right (Nat.succ_pos k),
   fun h => ⟨b - a - 1, by omega⟩⟩

theorem le_tri : ∀ n, n ≤ tri n
  | 0 => Nat.le_refl _
  | n + 1 => by have := le_tri n; simp only [tri]; omega

theorem le_npair_left (a b : Nat) : a ≤ npair a b := by
  have := le_tri (a + b); unfold npair; omega

theorem le_npair_right (a b : Nat) : b ≤ npair a b := by unfold npair; omega

/-! ## The β-function -/

def beta (s t i : Nat) : Nat := s % ((i + 1) * t + 1)

theorem mod_iff (s m x : Nat) (hm : 0 < m) :
    (∃ q, s = q * m + x ∧ x < m) ↔ s % m = x := by
  constructor
  · rintro ⟨q, rfl, hx⟩
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  · rintro rfl
    refine ⟨s / m, ?_, Nat.mod_lt _ hm⟩
    have := Nat.div_add_mod s m
    rw [Nat.mul_comm] at this; omega

/-! ## Every list is coded by a β-pair (Chinese remainder theorem) -/

/-- Bézout in `Int`. -/
theorem bezout (m n : Nat) : ∃ x y : Int, x * m + y * n = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
    obtain ⟨x, y, h⟩ := ih
    rw [Nat.gcd_rec m n]
    refine ⟨y - x * (n / m : Nat), x, ?_⟩
    have hd : ((n % m : Nat) : Int) = (n : Int) - (m : Int) * ((n / m : Nat) : Int) := by
      have := Nat.mod_add_div n m
      omega
    rw [hd, Int.mul_sub] at h
    rw [Int.sub_mul]
    have e1 : x * (↑m * ↑(n / m)) = x * ↑(n / m) * ↑m := by
      rw [Int.mul_comm (m : Int), Int.mul_assoc]
    rw [e1] at h
    omega

/-- Solving one congruence on top of others. -/
theorem crt_step (M n s a : Nat) (h : Nat.Coprime M n) (hn : 0 < n) :
    ∃ j, (s + j * M) % n = a % n := by
  obtain ⟨x, y, hxy⟩ := bezout M n
  rw [h] at hxy
  -- `x * M ≡ 1 (mod n)`; take `j ≡ x (a - s)`.
  let j : Int := (x * ((a : Int) - s)) % n
  have hj : 0 ≤ j := Int.emod_nonneg _ (by omega)
  refine ⟨j.toNat, ?_⟩
  have hcast : ((s + j.toNat * M : Nat) : Int) % n = (a : Int) % n := by
    have e : ((s + j.toNat * M : Nat) : Int) = s + j * M := by
      rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hj]
    rw [e]
    have h1 : (s + j * M : Int) % n = (s + (x * ((a : Int) - s)) * M) % n := by
      simp only [j]
      rw [Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ← Int.add_emod]
    rw [h1]
    have h2 : (s + (x * ((a : Int) - s)) * M : Int) = a + ((a : Int) - s) * (-y) * n := by
      have : x * (M : Int) = 1 - y * n := by omega
      calc (s + (x * ((a : Int) - s)) * M : Int)
          = s + ((a : Int) - s) * (x * M) := by
            rw [Int.mul_comm x, Int.mul_assoc]
        _ = s + ((a : Int) - s) * (1 - y * n) := by rw [this]
        _ = a + ((a : Int) - s) * (-y) * n := by
            rw [Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.neg_mul, Int.mul_neg]; omega
    rw [h2, Int.add_mul_emod_self_right]
  rw [← Int.natCast_emod, ← Int.natCast_emod] at hcast
  exact Int.ofNat.inj hcast

/-- A common multiple of `1, ..., n`. -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos : ∀ n, 0 < fac n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (by omega) (fac_pos n)

theorem dvd_fac : ∀ {k n : Nat}, 0 < k → k ≤ n → k ∣ fac n
  | _, 0, hk, hkn => by omega
  | k, n + 1, hk, hkn => by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact Nat.dvd_trans (dvd_fac hk (by omega)) (Nat.dvd_mul_left _ _)
    · have : k = n + 1 := by omega
      subst this; exact Nat.dvd_mul_right _ _

theorem coprime_succ_mul (i t : Nat) : Nat.Coprime ((i + 1) * t + 1) t := by
  show Nat.gcd _ _ = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.add_comm, Nat.add_mul_mod_self_right]
  rcases t with _ | _ | t <;> simp [Nat.mod_eq_of_lt]

/-- The moduli `1 + (i+1) t`, for `i < n` and `t = fac n`, are pairwise coprime. -/
theorem moduli_coprime {n i j : Nat} (hi : i < j) (hj : j < n) :
    Nat.Coprime ((i + 1) * fac n + 1) ((j + 1) * fac n + 1) := by
  let t := fac n
  let g := Nat.gcd ((i + 1) * t + 1) ((j + 1) * t + 1)
  have hg1 : g ∣ (i + 1) * t + 1 := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ (j + 1) * t + 1 := Nat.gcd_dvd_right _ _
  -- `g` divides the difference `(j - i) t`
  have hdiff : (j + 1) * t + 1 - ((i + 1) * t + 1) = (j - i) * t := by
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    rw [show i + d - i = d by omega, show i + d + 1 = (i + 1) + d by omega, Nat.add_mul]
    omega
  have hgd : g ∣ (j - i) * t := hdiff ▸ Nat.dvd_sub hg2 hg1
  -- `g` is coprime to `t`
  have hgt : Nat.Coprime g t :=
    Nat.Coprime.coprime_dvd_left hg1 (coprime_succ_mul i t)
  have hgji : g ∣ j - i := hgt.dvd_of_dvd_mul_right hgd
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle : g ≤ j - i := Nat.le_of_dvd (by omega) hgji
  have hgdt : g ∣ t := Nat.dvd_trans hgji (dvd_fac (by omega) (by omega))
  have : g ∣ 1 := by
    have h := Nat.dvd_sub hg1 (Nat.dvd_trans hgdt (Nat.dvd_mul_left t (i + 1)))
    rwa [Nat.add_sub_cancel_left] at h
  exact Nat.eq_one_of_dvd_one this

/-- The product of the first `k` moduli. -/
def modProd (t : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => modProd t k * ((k + 1) * t + 1)

theorem coprime_modProd {n k j : Nat} (hk : k ≤ j) (hj : j < n) :
    Nat.Coprime (modProd (fac n) k) ((j + 1) * fac n + 1) := by
  induction k with
  | zero => exact Nat.coprime_one_left _
  | succ k ih =>
    show Nat.Coprime (modProd (fac n) k * ((k + 1) * fac n + 1)) _
    exact Nat.coprime_mul_iff_left.mpr ⟨ih (by omega), moduli_coprime (by omega) hj⟩

theorem dvd_modProd {t k i : Nat} (hi : i < k) : ((i + 1) * t + 1) ∣ modProd t k := by
  induction k with
  | zero => omega
  | succ k ih =>
    show _ ∣ modProd t k * ((k + 1) * t + 1)
    rcases Nat.lt_or_ge i k with h | h
    · exact Nat.dvd_trans (ih h) (Nat.dvd_mul_right _ _)
    · have : i = k := by omega
      subst this; exact Nat.dvd_mul_left _ _

/-- **Every finite sequence has a β-code.** -/
theorem beta_exists_aux (f : Nat → Nat) (n : Nat) (hf : ∀ i < n, f i < fac n + 1) :
    ∃ s, ∀ i < n, beta s (fac n) i = f i := by
  suffices h : ∀ k ≤ n, ∃ s, ∀ i < k, beta s (fac n) i = f i from h n (Nat.le_refl _)
  intro k
  induction k with
  | zero => intro _; exact ⟨0, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := crt_step (modProd (fac n) k) ((k + 1) * fac n + 1) s (f k)
      (coprime_modProd (Nat.le_refl _) (by omega)) (by omega)
    refine ⟨s + j * modProd (fac n) k, fun i hi => ?_⟩
    have hlt : ∀ i < n, f i < (i + 1) * fac n + 1 := fun i hi => by
      have := hf i hi
      have : fac n ≤ (i + 1) * fac n := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rcases Nat.lt_or_ge i k with h | h
    · rw [beta, ← hs i h, beta]
      obtain ⟨c, hc⟩ := dvd_modProd (t := fac n) h
      rw [hc, Nat.mul_comm, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have : i = k := by omega
      subst this
      rw [beta, hj, Nat.mod_eq_of_lt (hlt i (by omega))]

theorem le_fac : ∀ n, n ≤ fac n
  | 0 => by decide
  | n + 1 => by
    have := fac_pos n
    show n + 1 ≤ (n + 1) * fac n
    exact Nat.le_mul_of_pos_right _ this

theorem sum_bound (f : Nat → Nat) : ∀ n, ∃ B, ∀ i < n, f i ≤ B
  | 0 => ⟨0, fun i hi => by omega⟩
  | n + 1 => by
    obtain ⟨B, hB⟩ := sum_bound f n
    refine ⟨B + f n, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i n with h | h
    · have := hB i h; omega
    · have : i = n := by omega
      subst this; omega

/-- Moduli are taken large enough (`t = fac N`) to exceed every entry. -/
theorem beta_exists (f : Nat → Nat) (n : Nat) : ∃ s t, ∀ i < n, beta s t i = f i := by
  obtain ⟨B, hB⟩ := sum_bound f n
  -- pad the sequence so that its length bounds its entries
  let g : Nat → Nat := fun i => if i < n then f i else 0
  obtain ⟨s, hs⟩ := beta_exists_aux g (n + B) (fun i _ => by
    have := le_fac (n + B)
    simp only [g]; split
    · have := hB i (by assumption); omega
    · omega)
  exact ⟨s, fac (n + B), fun i hi => by rw [hs i (by omega)]; simp [g, hi]⟩

end Rz
