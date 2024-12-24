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
def cartesian_product (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') : DFA α (σ × σ') := {
  step := fun ⟨s₁, s₂⟩ a => (M₁.step s₁ a, M₂.step s₂ a),
  start := (M₁.start, M₂.start),
  accept := {s | p (s.fst ∈ M₁.accept) (s.snd ∈ M₂.accept)}
}

theorem cartesian_product_accept_iff (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (s : σ × σ') :
    s ∈ (cartesian_product p M₁ M₂).accept ↔ p (s.fst ∈ M₁.accept) (s.snd ∈ M₂.accept) := by
  simp [cartesian_product]

theorem cartesian_product_eval_from (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    ∀ s : σ × σ',
    (cartesian_product p M₁ M₂).evalFrom s x = ⟨M₁.evalFrom s.1 x, M₂.evalFrom s.2 x⟩ := by
  dsimp [DFA.evalFrom, cartesian_product]
  induction' x with a x' ih
  · simp
  · intro s
    simp [List.foldl, ih, DFA.step]

theorem cartesian_product_accepts_iff (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    x ∈ (cartesian_product p M₁ M₂).accepts ↔ p (x ∈ M₁.accepts) (x ∈ M₂.accepts) := by
  simp [DFA.accepts]
  simp [DFA.acceptsFrom, cartesian_product_eval_from]
  simp [cartesian_product]
  repeat rw [Set.mem_setOf_eq]

def intersect (M₁ : DFA α σ) (M₂ : DFA α σ') : DFA α (σ × σ') := cartesian_product And M₁ M₂

theorem intersect_accept_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (s : σ × σ') :
    s ∈ (intersect M₁ M₂).accept ↔ s.fst ∈ M₁.accept ∧ s.snd ∈ M₂.accept := by
  simp [intersect, cartesian_product_accept_iff]

theorem intersect_accepts_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    x ∈ (intersect M₁ M₂).accepts ↔ x ∈ M₁.accepts ∧ x ∈ M₂.accepts := by
  simp [intersect, cartesian_product_accepts_iff]
