import PeanoPlaying.Truth

/-!
# Typing and normalization of System T, inside HA

We express in HA, over the Cantor codes `code : Term → Nat` of `Basic.lean`:

* `Typed(c)`: `c` codes a closed term of type `nat`;
* `Norm(c, n)`: `c` codes a term that weak-head normalizes to `numeral n`;

and the **normalization statement** `∀c. ∃n. Typed(c) ⊃ Norm(c, n)`.

Both are inductive relations on codes, expressed by the usual device of
*derivation tables*: `Der_R(f)` says there is a table, coded by a β-pair
`(s, t)` of some length `len`, that contains the fact `f`, and every entry
of which follows by one rule of `R` from entries with smaller index. The
rules are listed once as HA formulas (`JustTy`, `JustRed`), and once as Lean
propositions (`RTy`, `RRed`); `sat_JustTy` and `sat_JustRed` say they agree.

Facts are nested Cantor pairs, with a tag in the first component. Types are
coded by `nat ↦ 0`, `A ⟶ B ↦ ⟨1, ⟨A, B⟩⟩`, `A ⊗ B ↦ ⟨2, ⟨A, B⟩⟩`, and
contexts by `[] ↦ 0`, `A :: Γ ↦ ⟨A, Γ⟩ + 1`.
-/

namespace Rz

open DSL

/-! ## DSL extras -/

namespace DSL

/-- `let p := ⟨a, b⟩ in k p` -/
@[simp] def letP (a b : T) (k : T → F) : F := fEx fun p => fAnd (fP a b p) (k p)

/-- Trees of pairs. -/
inductive PT where
  | v : T → PT
  | n : Nat → PT
  | s : PT → PT
  | p : PT → PT → PT

@[simp] def build : PT → (T → F) → F
  | .v a, k => k a
  | .n m, k => k (tN m)
  | .s a, k => build a fun x => k (tS x)
  | .p a b, k => build a fun x => build b fun y => letP x y k

/-- `x` is the value of the tree `pt`. -/
@[simp] def fIs (x : T) (pt : PT) : F := build pt fun y => fEq x y

/-- `y` occurs at an index below `i` in the table `(s, t)`. -/
@[simp] def fE (s t i y : T) : F := fEx fun j => fAnd (fLt j i) (fBeta s t j y)

/-- The value of `pt` occurs below `i`. -/
@[simp] def fPrem (s t i : T) (pt : PT) : F := build pt (fE s t i)

/-- Tag disjunctions. -/
@[simp] def fTag (g : T) : List Nat → F
  | [] => fBot
  | [a] => fEq g (tN a)
  | a :: as => fOr (fEq g (tN a)) (fTag g as)

end DSL

theorem sat_fLt_lv (e : Nat → Nat) (a b d : Nat) (ha : a < d) (hb : b < d) :
    sat e (fLt (lv a) (lv b) d) ↔ e (d - a - 1) < e (d - b - 1) := by
  simp only [fLt, fEx, fEq, tAdd, tS, sat_ex, sat_eq, eval_add, eval_lv, eval_succ]
  rw [show d + 1 - a - 1 = (d - a - 1) + 1 by omega, show d + 1 - b - 1 = (d - b - 1) + 1 by omega,
    show d + 1 - d - 1 = 0 by omega]
  simp only [scons_succ, scons_zero, exists_add_succ]

theorem sat_fBeta_lv (e : Nat → Nat) (a b c x d : Nat) (ha : a < d) (hb : b < d) (hc : c < d)
    (hx : x < d) :
    sat e (fBeta (lv a) (lv b) (lv c) (lv x) d) ↔
      beta (e (d - a - 1)) (e (d - b - 1)) (e (d - c - 1)) = e (d - x - 1) := by
  simp only [fBeta, fEx, fAnd, fEq, tAdd, tMul, tS, sat_ex, sat_and, sat_eq, eval_add, eval_mul,
    eval_lv, eval_succ]
  rw [show d + 1 - a - 1 = (d - a - 1) + 1 by omega, show d + 1 - b - 1 = (d - b - 1) + 1 by omega,
    show d + 1 - c - 1 = (d - c - 1) + 1 by omega, show d + 1 - x - 1 = (d - x - 1) + 1 by omega,
    show d + 2 - b - 1 = (d - b - 1) + 2 by omega, show d + 2 - c - 1 = (d - c - 1) + 2 by omega,
    show d + 2 - x - 1 = (d - x - 1) + 2 by omega,
    show d + 1 - d - 1 = 0 by omega, show d + 2 - (d + 1) - 1 = 0 by omega]
  simp only [scons_succ, scons_zero, exists_add_succ]
  rw [beta, ← mod_iff _ _ _ (by omega)]

attribute [simp] sat_fLt_lv sat_fBeta_lv

/-! ## Codes of types, contexts and facts -/

def tyCode : Ty → Nat
  | .nat => 0
  | .arrow A B => npair 1 (npair (tyCode A) (tyCode B))
  | .prod A B => npair 2 (npair (tyCode A) (tyCode B))

def ctxCode : List Ty → Nat
  | [] => 0
  | A :: Γ => npair (tyCode A) (ctxCode Γ) + 1

/-- Typing facts `Γ ⊢ t : A` and lookup facts `Γ[k] = A`. -/
def tyF (G a A : Nat) : Nat := npair 0 (npair G (npair a A))
def lkF (G k A : Nat) : Nat := npair 1 (npair G (npair k A))

/-- Reduction facts: shifting, substitution, weak-head steps, weak-head
normalization, and numerals. -/
def shF (c d t r : Nat) : Nat := npair 0 (npair c (npair d (npair t r)))
def sbF (k t u r : Nat) : Nat := npair 1 (npair k (npair t (npair u r)))
def whF (t r : Nat) : Nat := npair 2 (npair t r)
def wnF (t r : Nat) : Nat := npair 3 (npair t r)
def numF (x n : Nat) : Nat := npair 4 (npair x n)

/-- Codes of `rect z s t`. -/
def rectC (z s t : Nat) : Nat := npair 5 (npair z (npair s t))

namespace DSL
open PT
@[simp] def tyP (G a A : PT) : PT := p (n 0) (p G (p a A))
@[simp] def lkP (G k A : PT) : PT := p (n 1) (p G (p k A))
@[simp] def shP (c d t r : PT) : PT := p (n 0) (p c (p d (p t r)))
@[simp] def sbP (k t u r : PT) : PT := p (n 1) (p k (p t (p u r)))
@[simp] def whP (t r : PT) : PT := p (n 2) (p t r)
@[simp] def wnP (t r : PT) : PT := p (n 3) (p t r)
@[simp] def numP (x m : PT) : PT := p (n 4) (p x m)
@[simp] def rectP (z s t : PT) : PT := p (n 5) (p z (p s t))
@[simp] def arrP (A B : PT) : PT := p (n 1) (p A B)
@[simp] def prodP (A B : PT) : PT := p (n 2) (p A B)
end DSL

namespace DSL
abbrev pv := PT.v
abbrev pn := PT.n
abbrev ps := PT.s
abbrev pp := PT.p
end DSL

/-! ## Typing rules -/

section Typing
variable (s t i x : T)

def tyRules : List F := [
  -- `(A :: Γ)[0] = A`
  fEx fun A => fEx fun G => fIs x (lkP (ps (pp (pv A) (pv G))) (pn 0) (pv A)),
  -- `(B :: Γ)[k+1] = Γ[k]`
  fEx fun A => fEx fun B => fEx fun G => fEx fun k =>
    fAnd (fIs x (lkP (ps (pp (pv B) (pv G))) (ps (pv k)) (pv A))) (fPrem s t i (lkP (pv G) (pv k) (pv A))),
  -- var
  fEx fun G => fEx fun m => fEx fun A =>
    fAnd (fIs x (tyP (pv G) (pp (pn 0) (pv m)) (pv A))) (fPrem s t i (lkP (pv G) (pv m) (pv A))),
  -- app
  fEx fun G => fEx fun a => fEx fun b => fEx fun A => fEx fun B =>
    fAnds [fIs x (tyP (pv G) (pp (pn 1) (pp (pv a) (pv b))) (pv B)),
      fPrem s t i (tyP (pv G) (pv a) (arrP (pv A) (pv B))),
      fPrem s t i (tyP (pv G) (pv b) (pv A))],
  -- lam
  fEx fun G => fEx fun a => fEx fun A => fEx fun B =>
    fAnd (fIs x (tyP (pv G) (pp (pn 2) (pv a)) (arrP (pv A) (pv B))))
      (fPrem s t i (tyP (ps (pp (pv A) (pv G))) (pv a) (pv B))),
  -- zero
  fEx fun G => fIs x (tyP (pv G) (pp (pn 3) (pn 0)) (pn 0)),
  -- succ
  fEx fun G => fEx fun a =>
    fAnd (fIs x (tyP (pv G) (pp (pn 4) (pv a)) (pn 0))) (fPrem s t i (tyP (pv G) (pv a) (pn 0))),
  -- rect
  fEx fun G => fEx fun z => fEx fun f => fEx fun a => fEx fun A =>
    fAnds [fIs x (tyP (pv G) (rectP (pv z) (pv f) (pv a)) (pv A)),
      fPrem s t i (tyP (pv G) (pv z) (pv A)),
      fPrem s t i (tyP (pv G) (pv f) (arrP (pn 0) (arrP (pv A) (pv A)))),
      fPrem s t i (tyP (pv G) (pv a) (pn 0))],
  -- pair
  fEx fun G => fEx fun a => fEx fun b => fEx fun A => fEx fun B =>
    fAnds [fIs x (tyP (pv G) (pp (pn 6) (pp (pv a) (pv b))) (prodP (pv A) (pv B))),
      fPrem s t i (tyP (pv G) (pv a) (pv A)),
      fPrem s t i (tyP (pv G) (pv b) (pv B))],
  -- fst
  fEx fun G => fEx fun a => fEx fun A => fEx fun B =>
    fAnd (fIs x (tyP (pv G) (pp (pn 7) (pv a)) (pv A))) (fPrem s t i (tyP (pv G) (pv a) (prodP (pv A) (pv B)))),
  -- snd
  fEx fun G => fEx fun a => fEx fun A => fEx fun B =>
    fAnd (fIs x (tyP (pv G) (pp (pn 8) (pv a)) (pv B))) (fPrem s t i (tyP (pv G) (pv a) (prodP (pv A) (pv B))))]

end Typing

/-- The typing rules as Lean propositions; `E` holds of the earlier facts. -/
def RTy (E : Nat → Prop) (x : Nat) : Prop :=
  (∃ A G, x = lkF (npair A G + 1) 0 A) ∨
  (∃ A B G k, x = lkF (npair B G + 1) (k + 1) A ∧ E (lkF G k A)) ∨
  (∃ G m A, x = tyF G (npair 0 m) A ∧ E (lkF G m A)) ∨
  (∃ G a b A B, x = tyF G (npair 1 (npair a b)) B ∧
    E (tyF G a (npair 1 (npair A B))) ∧ E (tyF G b A)) ∨
  (∃ G a A B, x = tyF G (npair 2 a) (npair 1 (npair A B)) ∧ E (tyF (npair A G + 1) a B)) ∨
  (∃ G, x = tyF G (npair 3 0) 0) ∨
  (∃ G a, x = tyF G (npair 4 a) 0 ∧ E (tyF G a 0)) ∨
  (∃ G z f a A, x = tyF G (rectC z f a) A ∧ E (tyF G z A) ∧
    E (tyF G f (npair 1 (npair 0 (npair 1 (npair A A))))) ∧ E (tyF G a 0)) ∨
  (∃ G a b A B, x = tyF G (npair 6 (npair a b)) (npair 2 (npair A B)) ∧
    E (tyF G a A) ∧ E (tyF G b B)) ∨
  (∃ G a A B, x = tyF G (npair 7 a) A ∧ E (tyF G a (npair 2 (npair A B)))) ∨
  (∃ G a A B, x = tyF G (npair 8 a) B ∧ E (tyF G a (npair 2 (npair A B))))

/-! ## Reduction rules -/

section Reduction
variable (s t i x : T)

def redRules : List F := [
  -- shift, variable below the cutoff
  fEx fun c => fEx fun d => fEx fun j =>
    fAnd (fIs x (shP (pv c) (pv d) (pp (pn 0) (pv j)) (pp (pn 0) (pv j)))) (fLt j c),
  -- shift, variable above the cutoff
  fEx fun c => fEx fun d => fEx fun m =>
    fIs x (shP (pv c) (pv d) (pp (pn 0) (pv (tAdd c m))) (pp (pn 0) (pv (tAdd (tAdd c m) d)))),
  -- shift, lam
  fEx fun c => fEx fun d => fEx fun a => fEx fun r =>
    fAnd (fIs x (shP (pv c) (pv d) (pp (pn 2) (pv a)) (pp (pn 2) (pv r))))
      (fPrem s t i (shP (ps (pv c)) (pv d) (pv a) (pv r))),
  -- shift, zero
  fEx fun c => fEx fun d => fIs x (shP (pv c) (pv d) (pp (pn 3) (pn 0)) (pp (pn 3) (pn 0))),
  -- shift, unary constructors `succ`, `fst`, `snd`
  fEx fun g => fEx fun c => fEx fun d => fEx fun a => fEx fun r =>
    fAnds [fTag g [4, 7, 8], fIs x (shP (pv c) (pv d) (pp (pv g) (pv a)) (pp (pv g) (pv r))),
      fPrem s t i (shP (pv c) (pv d) (pv a) (pv r))],
  -- shift, binary constructors `app`, `pair`
  fEx fun g => fEx fun c => fEx fun d => fEx fun a => fEx fun b => fEx fun a' => fEx fun b' =>
    fAnds [fTag g [1, 6],
      fIs x (shP (pv c) (pv d) (pp (pv g) (pp (pv a) (pv b))) (pp (pv g) (pp (pv a') (pv b')))),
      fPrem s t i (shP (pv c) (pv d) (pv a) (pv a')), fPrem s t i (shP (pv c) (pv d) (pv b) (pv b'))],
  -- shift, rect
  fEx fun c => fEx fun d => fEx fun z => fEx fun f => fEx fun a =>
  fEx fun z' => fEx fun f' => fEx fun a' =>
    fAnds [fIs x (shP (pv c) (pv d) (rectP (pv z) (pv f) (pv a)) (rectP (pv z') (pv f') (pv a'))),
      fPrem s t i (shP (pv c) (pv d) (pv z) (pv z')), fPrem s t i (shP (pv c) (pv d) (pv f) (pv f')),
      fPrem s t i (shP (pv c) (pv d) (pv a) (pv a'))],
  -- substitution, variable below the index
  fEx fun k => fEx fun u => fEx fun j =>
    fAnd (fIs x (sbP (pv k) (pp (pn 0) (pv j)) (pv u) (pp (pn 0) (pv j)))) (fLt j k),
  -- substitution, the variable itself
  fEx fun k => fEx fun u => fEx fun r =>
    fAnd (fIs x (sbP (pv k) (pp (pn 0) (pv k)) (pv u) (pv r))) (fPrem s t i (shP (pn 0) (pv k) (pv u) (pv r))),
  -- substitution, variable above the index
  fEx fun k => fEx fun u => fEx fun m =>
    fIs x (sbP (pv k) (pp (pn 0) (ps (pv (tAdd k m)))) (pv u) (pp (pn 0) (pv (tAdd k m)))),
  -- substitution, lam
  fEx fun k => fEx fun a => fEx fun u => fEx fun r =>
    fAnd (fIs x (sbP (pv k) (pp (pn 2) (pv a)) (pv u) (pp (pn 2) (pv r))))
      (fPrem s t i (sbP (ps (pv k)) (pv a) (pv u) (pv r))),
  -- substitution, zero
  fEx fun k => fEx fun u => fIs x (sbP (pv k) (pp (pn 3) (pn 0)) (pv u) (pp (pn 3) (pn 0))),
  -- substitution, unary constructors
  fEx fun g => fEx fun k => fEx fun a => fEx fun u => fEx fun r =>
    fAnds [fTag g [4, 7, 8], fIs x (sbP (pv k) (pp (pv g) (pv a)) (pv u) (pp (pv g) (pv r))),
      fPrem s t i (sbP (pv k) (pv a) (pv u) (pv r))],
  -- substitution, binary constructors
  fEx fun g => fEx fun k => fEx fun a => fEx fun b => fEx fun u => fEx fun a' => fEx fun b' =>
    fAnds [fTag g [1, 6],
      fIs x (sbP (pv k) (pp (pv g) (pp (pv a) (pv b))) (pv u) (pp (pv g) (pp (pv a') (pv b')))),
      fPrem s t i (sbP (pv k) (pv a) (pv u) (pv a')), fPrem s t i (sbP (pv k) (pv b) (pv u) (pv b'))],
  -- substitution, rect
  fEx fun k => fEx fun z => fEx fun f => fEx fun a => fEx fun u =>
  fEx fun z' => fEx fun f' => fEx fun a' =>
    fAnds [fIs x (sbP (pv k) (rectP (pv z) (pv f) (pv a)) (pv u) (rectP (pv z') (pv f') (pv a'))),
      fPrem s t i (sbP (pv k) (pv z) (pv u) (pv z')), fPrem s t i (sbP (pv k) (pv f) (pv u) (pv f')),
      fPrem s t i (sbP (pv k) (pv a) (pv u) (pv a'))],
  -- weak head: `app t u ⟶ app t' u`
  fEx fun a => fEx fun b => fEx fun a' =>
    fAnd (fIs x (whP (pp (pn 1) (pp (pv a) (pv b))) (pp (pn 1) (pp (pv a') (pv b)))))
      (fPrem s t i (whP (pv a) (pv a'))),
  -- weak head: β
  fEx fun a => fEx fun b => fEx fun r =>
    fAnd (fIs x (whP (pp (pn 1) (pp (pp (pn 2) (pv a)) (pv b))) (pv r)))
      (fPrem s t i (sbP (pn 0) (pv a) (pv b) (pv r))),
  -- weak head: `rect z s t ⟶ rect z s t'`
  fEx fun z => fEx fun f => fEx fun a => fEx fun a' =>
    fAnd (fIs x (whP (rectP (pv z) (pv f) (pv a)) (rectP (pv z) (pv f) (pv a'))))
      (fPrem s t i (whP (pv a) (pv a'))),
  -- weak head: under `succ`, `fst`, `snd`
  fEx fun g => fEx fun a => fEx fun a' =>
    fAnds [fTag g [4, 7, 8], fIs x (whP (pp (pv g) (pv a)) (pp (pv g) (pv a'))),
      fPrem s t i (whP (pv a) (pv a'))],
  -- weak head: `rect z s 0 ⟶ z`
  fEx fun z => fEx fun f => fIs x (whP (rectP (pv z) (pv f) (pp (pn 3) (pn 0))) (pv z)),
  -- weak head: `rect z s (succ t) ⟶ s t (rect z s t)`
  fEx fun z => fEx fun f => fEx fun a =>
    fIs x (whP (rectP (pv z) (pv f) (pp (pn 4) (pv a)))
      (pp (pn 1) (pp (pp (pn 1) (pp (pv f) (pv a))) (rectP (pv z) (pv f) (pv a))))),
  -- weak head: projections
  fEx fun a => fEx fun b => fIs x (whP (pp (pn 7) (pp (pn 6) (pp (pv a) (pv b)))) (pv a)),
  fEx fun a => fEx fun b => fIs x (whP (pp (pn 8) (pp (pn 6) (pp (pv a) (pv b)))) (pv b)),
  -- weak head normalization
  fEx fun a => fIs x (wnP (pv a) (pv a)),
  fEx fun a => fEx fun a' => fEx fun r =>
    fAnds [fIs x (wnP (pv a) (pv r)), fPrem s t i (whP (pv a) (pv a')), fPrem s t i (wnP (pv a') (pv r))],
  -- numerals
  fIs x (numP (pp (pn 3) (pn 0)) (pn 0)),
  fEx fun y => fEx fun m =>
    fAnd (fIs x (numP (pp (pn 4) (pv y)) (ps (pv m)))) (fPrem s t i (numP (pv y) (pv m)))]

end Reduction

def RRed (E : Nat → Prop) (x : Nat) : Prop :=
  (∃ c d j, x = shF c d (npair 0 j) (npair 0 j) ∧ j < c) ∨
  (∃ c d m, x = shF c d (npair 0 (c + m)) (npair 0 (c + m + d))) ∨
  (∃ c d a r, x = shF c d (npair 2 a) (npair 2 r) ∧ E (shF (c + 1) d a r)) ∨
  (∃ c d, x = shF c d (npair 3 0) (npair 3 0)) ∨
  (∃ g c d a r, (g = 4 ∨ g = 7 ∨ g = 8) ∧ x = shF c d (npair g a) (npair g r) ∧ E (shF c d a r)) ∨
  (∃ g c d a b a' b', (g = 1 ∨ g = 6) ∧
    x = shF c d (npair g (npair a b)) (npair g (npair a' b')) ∧
    E (shF c d a a') ∧ E (shF c d b b')) ∨
  (∃ c d z f a z' f' a', x = shF c d (rectC z f a) (rectC z' f' a') ∧
    E (shF c d z z') ∧ E (shF c d f f') ∧ E (shF c d a a')) ∨
  (∃ k u j, x = sbF k (npair 0 j) u (npair 0 j) ∧ j < k) ∨
  (∃ k u r, x = sbF k (npair 0 k) u r ∧ E (shF 0 k u r)) ∨
  (∃ k u m, x = sbF k (npair 0 (k + m + 1)) u (npair 0 (k + m))) ∨
  (∃ k a u r, x = sbF k (npair 2 a) u (npair 2 r) ∧ E (sbF (k + 1) a u r)) ∨
  (∃ k u, x = sbF k (npair 3 0) u (npair 3 0)) ∨
  (∃ g k a u r, (g = 4 ∨ g = 7 ∨ g = 8) ∧ x = sbF k (npair g a) u (npair g r) ∧
    E (sbF k a u r)) ∨
  (∃ g k a b u a' b', (g = 1 ∨ g = 6) ∧
    x = sbF k (npair g (npair a b)) u (npair g (npair a' b')) ∧
    E (sbF k a u a') ∧ E (sbF k b u b')) ∨
  (∃ k z f a u z' f' a', x = sbF k (rectC z f a) u (rectC z' f' a') ∧
    E (sbF k z u z') ∧ E (sbF k f u f') ∧ E (sbF k a u a')) ∨
  (∃ a b a', x = whF (npair 1 (npair a b)) (npair 1 (npair a' b)) ∧ E (whF a a')) ∨
  (∃ a b r, x = whF (npair 1 (npair (npair 2 a) b)) r ∧ E (sbF 0 a b r)) ∨
  (∃ z f a a', x = whF (rectC z f a) (rectC z f a') ∧ E (whF a a')) ∨
  (∃ g a a', (g = 4 ∨ g = 7 ∨ g = 8) ∧ x = whF (npair g a) (npair g a') ∧ E (whF a a')) ∨
  (∃ z f, x = whF (rectC z f (npair 3 0)) z) ∨
  (∃ z f a, x = whF (rectC z f (npair 4 a)) (npair 1 (npair (npair 1 (npair f a)) (rectC z f a)))) ∨
  (∃ a b, x = whF (npair 7 (npair 6 (npair a b))) a) ∨
  (∃ a b, x = whF (npair 8 (npair 6 (npair a b))) b) ∨
  (∃ a, x = wnF a a) ∨
  (∃ a a' r, x = wnF a r ∧ E (whF a a') ∧ E (wnF a' r)) ∨
  (x = numF (npair 3 0) 0) ∨
  (∃ y m, x = numF (npair 4 y) (m + 1) ∧ E (numF y m))

/-! ## The rule formulas, and their meaning

The rule formulas have four free variables: the table `(s, t)` as
variables `3, 2`, the index `i` as variable `1`, and the fact `x` as
variable `0`. -/

def JustTy : HA.Formula := fOrs (tyRules (lv 0) (lv 1) (lv 2) (lv 3)) 4
def JustRed : HA.Formula := fOrs (redRules (lv 0) (lv 1) (lv 2) (lv 3)) 4

/-- The facts below index `i` of the table `(s, t)`. -/
def Below (s t i : Nat) : Nat → Prop := fun y => ∃ j < i, beta s t j = y

set_option maxHeartbeats 4000000 in
theorem sat_JustTy (e : Nat → Nat) : sat e JustTy ↔ RTy (Below (e 3) (e 2) (e 1)) (e 0) := by
  simp [JustTy, tyRules, fOrs, fAnds, RTy, Below, tyF, lkF, rectC]

set_option maxHeartbeats 4000000 in
theorem sat_JustRed (e : Nat → Nat) : sat e JustRed ↔ RRed (Below (e 3) (e 2) (e 1)) (e 0) := by
  simp [JustRed, redRules, fOrs, fAnds, RRed, Below, shF, sbF, whF, wnF, numF, rectC]

/-! ## Derivation tables -/

/-- Substitution of the rule variables `s, t, i, x`. -/
def ruleσ (s t i x : HA.Tm) : Nat → HA.Tm
  | 0 => x
  | 1 => i
  | 2 => t
  | 3 => s
  | _ => .zero

namespace DSL
/-- Plug a rule formula in. -/
def fRule (J : HA.Formula) (s t i x : T) : F := fun d => J.subst (ruleσ (s d) (t d) (i d) (x d))

/-- `Der_J(f)`: some table, every entry of which follows by `J` from
earlier ones, contains `f`. -/
def fDer (J : HA.Formula) (f : T) : F :=
  fEx fun s => fEx fun t => fEx fun len =>
    fAnd (fBex len fun i => fBeta s t i f)
      (fBall len fun i => fEx fun x => fAnd (fBeta s t i x) (fRule J s t i x))
end DSL

/-- The semantic counterpart of `fDer`. -/
def DerSem (R : (Nat → Prop) → Nat → Prop) (f : Nat) : Prop :=
  ∃ s t len, (∃ i < len, beta s t i = f) ∧ ∀ i < len, R (Below s t i) (beta s t i)

theorem eval_subst (e : Nat → Nat) (σ : Nat → HA.Tm) (a : HA.Tm) :
    eval e (a.subst σ) = eval (fun k => eval e (σ k)) a := by
  induction a <;> simp_all [HA.Tm.subst, eval]

theorem sat_subst (φ : HA.Formula) : ∀ (e : Nat → Nat) (σ : Nat → HA.Tm),
    sat e (φ.subst σ) ↔ sat (fun k => eval e (σ k)) φ := by
  have hup : ∀ (e : Nat → Nat) (σ : Nat → HA.Tm) (n : Nat),
      (fun k => eval (scons n e) (HA.Tm.up σ k)) = scons n (fun k => eval e (σ k)) := by
    intro e σ n; funext k; cases k with
    | zero => rfl
    | succ k =>
      show eval (scons n e) ((σ k).subst HA.Tm.shift) = _
      rw [eval_subst]; rfl
  induction φ with
  | eq a b => intro e σ; simp [HA.Formula.subst, eval_subst]
  | bot => intro e σ; rfl
  | and φ ψ ih₁ ih₂ => intro e σ; simp [HA.Formula.subst, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro e σ; simp [HA.Formula.subst, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => intro e σ; simp [HA.Formula.subst, ih₁, ih₂]
  | ex φ ih => intro e σ; simp only [HA.Formula.subst, sat_ex, ih, hup]
  | all φ ih => intro e σ; simp only [HA.Formula.subst, sat_all, ih, hup]

theorem sat_fRule (J : HA.Formula) (R : (Nat → Prop) → Nat → Prop)
    (hJ : ∀ e, sat e J ↔ R (Below (e 3) (e 2) (e 1)) (e 0))
    (e : Nat → Nat) (s t i x : T) (d : Nat) :
    sat e (fRule J s t i x d) ↔
      R (Below (eval e (s d)) (eval e (t d)) (eval e (i d))) (eval e (x d)) := by
  rw [fRule, sat_subst, hJ]; rfl

/-! ## The statement -/

/-- `Typed(c)`, with `c` the variable bound at level `0`. -/
def TypedD (c : T) : F := build (tyP (pn 0) (pv c) (pn 0)) (fDer JustTy)

/-- `Norm(c, m)`. -/
def NormD (c m : T) : F :=
  fEx fun y => fAnd (build (wnP (pv c) (pv y)) (fDer JustRed)) (build (numP (pv y) (pv m)) (fDer JustRed))

/-- `Typed(c)` and `Norm(c, m)` as formulas with `c` as variable `1` and `m`
as variable `0`. -/
def Typed : HA.Formula := TypedD (lv 0) 2
def Norm : HA.Formula := NormD (lv 0) (lv 1) 2

/-- **The normalization statement**: every code of a closed term of type
`nat` has a value `n`, i.e. the term weak-head normalizes to `numeral n`. -/
def NormStmt : HA.Formula := .all (.ex (.imp Typed Norm))

set_option maxHeartbeats 4000000 in
theorem sat_Typed (e : Nat → Nat) : sat e Typed ↔ DerSem RTy (tyF 0 (e 1) 0) := by
  simp [Typed, TypedD, fDer, sat_fRule _ _ sat_JustTy, DerSem, tyF, exists_add_succ]

set_option maxHeartbeats 4000000 in
theorem sat_Norm (e : Nat → Nat) :
    sat e Norm ↔ ∃ y, DerSem RRed (wnF (e 1) y) ∧ DerSem RRed (numF y (e 0)) := by
  simp [Norm, NormD, fDer, sat_fRule _ _ sat_JustRed, DerSem, wnF, numF, exists_add_succ]

/-! ## Shape of the statement -/

macro "sig_tac" : tactic => `(tactic| repeat (first
  | apply Sig.eq | apply Sig.bot | apply Sig.and | apply Sig.or | apply Sig.ex
  | apply Sig.ball))

macro "pos_tac" : tactic => `(tactic| repeat (first
  | apply Pos.eq | apply Pos.bot | apply Pos.and | apply Pos.or | apply Pos.ex | apply Pos.all
  | (apply Pos.imp; · sig_tac; done)))

theorem sig_Typed : Sig Typed := by
  unfold Typed TypedD
  sig_tac

theorem pos_Norm : Pos Norm := by
  unfold Norm NormD
  pos_tac

end Rz
