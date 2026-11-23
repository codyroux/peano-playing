import PeanoPlaying.Encode

/-!
# Completeness of the typing encoding

`typed_complete`: if `t` is a closed term of type `nat`, then `Typed(⌜t⌝)` is
true. A typing derivation is flattened into a list in which every entry
follows from earlier ones (`Valid`), which is then coded by a β-pair.
-/

namespace Rz

open Term

/-! ## Valid lists -/

/-- Every entry follows by `R` from the entries before it. -/
def Valid (R : (Nat → Prop) → Nat → Prop) (L : List Nat) : Prop :=
  ∀ i (h : i < L.length), R (fun y => y ∈ L.take i) L[i]

def Mono (R : (Nat → Prop) → Nat → Prop) : Prop :=
  ∀ (E E' : Nat → Prop) (x : Nat), (∀ y, E y → E' y) → R E x → R E' x

theorem Valid.append {R} (hR : Mono R) {L₁ L₂ : List Nat} (h₁ : Valid R L₁) (h₂ : Valid R L₂) :
    Valid R (L₁ ++ L₂) := by
  intro i hi
  rcases Nat.lt_or_ge i L₁.length with h | h
  · rw [List.getElem_append_left h, List.take_append_of_le_length (by omega)]
    exact h₁ i h
  · have hj : i - L₁.length < L₂.length := by simp at hi; omega
    rw [List.getElem_append_right h]
    refine hR _ _ _ (fun y hy => ?_) (h₂ _ hj)
    rw [show i = L₁.length + (i - L₁.length) by omega, List.take_length_add_append]
    exact List.mem_append_right _ hy

theorem Valid.snoc {R} {L : List Nat} {x : Nat} (h : Valid R L) (hx : R (fun y => y ∈ L) x) :
    Valid R (L ++ [x]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with h' | h'
  · rw [List.getElem_append_left h', List.take_append_of_le_length (by omega)]
    exact h i h'
  · have : i = L.length := by omega
    subst this
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem_singleton, List.take_left']
    exact hx

theorem Valid.nil {R} : Valid R [] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- A valid list is a derivation table. -/
theorem Valid.der {R} (hR : Mono R) {L : List Nat} (h : Valid R L) {f : Nat} (hf : f ∈ L) :
    DerSem R f := by
  obtain ⟨s, t, hst⟩ := beta_exists (fun i => L.getD i 0) L.length
  have hb : ∀ i (hi : i < L.length), beta s t i = L[i] := fun i hi => by
    rw [hst i hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  refine ⟨s, t, L.length, ?_, fun i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
    exact ⟨i, hi, hb i hi⟩
  · rw [hb i hi]
    refine hR _ _ _ (fun y hy => ?_) (h i hi)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    simp only [List.length_take] at hj
    refine ⟨j, by omega, ?_⟩
    rw [hb j (by omega), List.getElem_take]

/-! ## The typing rules -/

theorem RTy.mono : Mono RTy := by
  intro E E' x hE h
  rcases h with h | ⟨A, B, G, k, rfl, h₁⟩ | ⟨G, m, A, rfl, h₁⟩ | ⟨G, a, b, A, B, rfl, h₁, h₂⟩ |
    ⟨G, a, A, B, rfl, h₁⟩ | h | ⟨G, a, rfl, h₁⟩ | ⟨G, z, f, a, A, rfl, h₁, h₂, h₃⟩ |
    ⟨G, a, b, A, B, rfl, h₁, h₂⟩ | ⟨G, a, A, B, rfl, h₁⟩ | ⟨G, a, A, B, rfl, h₁⟩
  · exact .inl h
  · exact .inr (.inl ⟨A, B, G, k, rfl, hE _ h₁⟩)
  · exact .inr (.inr (.inl ⟨G, m, A, rfl, hE _ h₁⟩))
  · exact .inr (.inr (.inr (.inl ⟨G, a, b, A, B, rfl, hE _ h₁, hE _ h₂⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨G, a, A, B, rfl, hE _ h₁⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨G, a, rfl, hE _ h₁⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨G, z, f, a, A, rfl, hE _ h₁, hE _ h₂, hE _ h₃⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨G, a, b, A, B, rfl, hE _ h₁, hE _ h₂⟩))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨G, a, A, B, rfl, hE _ h₁⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨G, a, A, B, rfl, hE _ h₁⟩)))))))))

/-- A single derivation step: from valid lists deriving the premises, a
valid list deriving the conclusion. -/
theorem Valid.flatten : ∀ {Ls : List (List Nat)}, (∀ L ∈ Ls, Valid RTy L) → Valid RTy Ls.flatten
  | [], _ => Valid.nil
  | L :: Ls, hv => by
    simp only [List.flatten_cons]
    exact Valid.append (R := RTy) RTy.mono (hv L (by simp))
      (Valid.flatten (fun L' h => hv L' (by simp [h])))

theorem mem_flat {Ls : List (List Nat)} {L : List Nat} {y : Nat} (hL : L ∈ Ls) (hy : y ∈ L) :
    y ∈ Ls.flatten := List.mem_flatten.mpr ⟨L, hL, hy⟩

theorem Valid.step {Ls : List (List Nat)} (hv : ∀ L ∈ Ls, Valid RTy L) {x : Nat}
    (hx : RTy (fun y => y ∈ Ls.flatten) x) : ∃ L, Valid RTy L ∧ x ∈ L :=
  ⟨_, (Valid.flatten hv).snoc hx, by simp⟩

theorem lookup_complete : ∀ (Γ : List Ty) (k : Nat) (h : k < Γ.length),
    ∃ L, Valid RTy L ∧ lkF (ctxCode Γ) k (tyCode Γ[k]) ∈ L
  | [], k, h => absurd h (Nat.not_lt_zero _)
  | A :: Γ, 0, _ => Valid.step (Ls := []) (by simp) (.inl ⟨tyCode A, ctxCode Γ, rfl⟩)
  | A :: Γ, k + 1, h => by
    obtain ⟨L, hL, hm⟩ := lookup_complete Γ k (by simp at h; omega)
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inl ⟨_, tyCode A, ctxCode Γ, k, rfl, mem_flat (by simp) hm⟩))

theorem typing_complete {Γ : List Ty} {t : Term} {A : Ty} (h : HasType Γ t A) :
    ∃ L, Valid RTy L ∧ tyF (ctxCode Γ) (code t) (tyCode A) ∈ L := by
  induction h with
  | @var n Γ hn =>
    obtain ⟨L, hL, hm⟩ := lookup_complete Γ n hn
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inr (.inl ⟨_, n, _, rfl, mem_flat (by simp) hm⟩)))
  | app _ _ ih₁ ih₂ =>
    obtain ⟨L₁, h₁, m₁⟩ := ih₁
    obtain ⟨L₂, h₂, m₂⟩ := ih₂
    exact Valid.step (Ls := [L₁, L₂]) (by simp [h₁, h₂])
      (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, rfl, mem_flat (by simp) m₁, mem_flat (by simp) m₂⟩))))
  | lam _ ih =>
    obtain ⟨L, hL, hm⟩ := ih
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, mem_flat (by simp) hm⟩)))))
  | zero => exact Valid.step (Ls := []) (by simp) (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩))))))
  | succ _ ih =>
    obtain ⟨L, hL, hm⟩ := ih
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, mem_flat (by simp) hm⟩)))))))
  | rect _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨L₁, h₁, m₁⟩ := ih₁
    obtain ⟨L₂, h₂, m₂⟩ := ih₂
    obtain ⟨L₃, h₃, m₃⟩ := ih₃
    exact Valid.step (Ls := [L₁, L₂, L₃]) (by simp [h₁, h₂, h₃])
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨_, _, _, _, _, rfl, mem_flat (by simp) m₁, mem_flat (by simp) m₂, mem_flat (by simp) m₃⟩))))))))
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨L₁, h₁, m₁⟩ := ih₁
    obtain ⟨L₂, h₂, m₂⟩ := ih₂
    exact Valid.step (Ls := [L₁, L₂]) (by simp [h₁, h₂])
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨_, _, _, _, _, rfl, mem_flat (by simp) m₁, mem_flat (by simp) m₂⟩)))))))))
  | fst _ ih =>
    obtain ⟨L, hL, hm⟩ := ih
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨_, _, _, _, rfl, mem_flat (by simp) hm⟩))))))))))
  | snd _ ih =>
    obtain ⟨L, hL, hm⟩ := ih
    exact Valid.step (Ls := [L]) (by simpa using hL)
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        ⟨_, _, _, _, rfl, mem_flat (by simp) hm⟩))))))))))

/-- **Completeness of `Typed`**. -/
theorem typed_complete {t : Term} (h : HasType [] t .nat) (m : Nat) :
    sat (scons m (scons (code t) (fun _ => 0))) Typed := by
  rw [sat_Typed]
  obtain ⟨L, hL, hm⟩ := typing_complete h
  exact hL.der RTy.mono hm

end Rz
