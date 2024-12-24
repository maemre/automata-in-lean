import Mathlib.Computability.DFA

variable {α : Type u} {σ : Type v} {σ' : Type v} (M : DFA α σ)

def invert (M : DFA α σ) : DFA α σ := {
  step := M.step,
  start := M.start,
  accept := M.acceptᶜ,
}

theorem invert_accept_iff (s : σ) : s ∈ (invert M).accept ↔ s ∉ M.accept := by
  simp [invert]

theorem invert_accepts_iff (x : List α) : x ∈ (invert M).accepts ↔ x ∉ M.accepts := by
  apply invert_accept_iff

-- Cartesian product of two DFAs with an arbitrary acceptance condition
def cartesian_product (p : Prop -> Prop -> Prop) (M1 : DFA α σ) (M2 : DFA α σ') : DFA α (σ × σ') := {
  step := fun ⟨s1, s2⟩ a => (M1.step s1 a, M2.step s2 a),
  start := (M1.start, M2.start),
  accept := {s | p (s.fst ∈ M1.accept) (s.snd ∈ M2.accept)}
}

theorem cartesian_product_accept_iff (p : Prop -> Prop -> Prop) (M1 : DFA α σ) (M2 : DFA α σ') (s : σ × σ') :
  s ∈ (cartesian_product p M1 M2).accept ↔ p (s.fst ∈ M1.accept) (s.snd ∈ M2.accept) := by
  simp [cartesian_product]

theorem cartesian_product_eval_from (p : Prop -> Prop -> Prop) (M1 : DFA α σ) (M2 : DFA α σ') (x : List α) :
  ∀ s : σ × σ',
  (cartesian_product p M1 M2).evalFrom s x = ⟨M1.evalFrom s.1 x, M2.evalFrom s.2 x⟩ := by
  dsimp [DFA.evalFrom, cartesian_product]
  induction' x with a x' ih
  · simp
  · intro s
    simp [List.foldl, ih, DFA.step]

theorem cartesian_product_accepts_iff (p : Prop -> Prop -> Prop) (M1 : DFA α σ) (M2 : DFA α σ') (x : List α) :
  x ∈ (cartesian_product p M1 M2).accepts ↔ p (x ∈ M1.accepts) (x ∈ M2.accepts) := by
  simp [DFA.accepts]
  simp [DFA.acceptsFrom, cartesian_product_eval_from]
  simp [cartesian_product]
  repeat rw [Set.mem_setOf_eq]

def intersect (M1 : DFA α σ) (M2 : DFA α σ') : DFA α (σ × σ') := cartesian_product And M1 M2

theorem intersect_accept_iff (M1 : DFA α σ) (M2 : DFA α σ') (s : σ × σ') :
  s ∈ (intersect M1 M2).accept ↔ s.fst ∈ M1.accept ∧ s.snd ∈ M2.accept := by
  simp [intersect, cartesian_product_accept_iff]

theorem intersect_accepts_iff (M1 : DFA α σ) (M2 : DFA α σ') (x : List α) :
  x ∈ (intersect M1 M2).accepts ↔ x ∈ M1.accepts ∧ x ∈ M2.accepts := by
  simp [intersect, cartesian_product_accepts_iff]
