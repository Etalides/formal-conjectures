module

public import Mathlib.Data.Bool.Basic

@[simp] lemma decide_le_decide {p q : Prop} [Decidable p] [Decidable q] :
    decide p ≤ decide q ↔ (p → q) := by by_cases p <;> by_cases q <;> simp [*]
