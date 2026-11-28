import Mathlib

-- Cut of L-goldbach-linnik-five-unconditional.
-- child 1 zh: 初段受限版本（变量≤ 10^12）：保留冻结阈值，仅限制到初始区间。
-- child 1 en: Initial-segment restriction (variable <= 10^12): keeps the frozen threshold, only restricts the range.
-- child 2 zh: 尾段受限版本（变量 > 10^12）：保留冻结阈值，只处理尾部区间。
-- child 2 en: Tail restriction (variable > 10^12): keeps the frozen threshold and covers only the tail range.
-- Both premises keep the frozen existential threshold and restrict the variable to one side of (10:ℕ)^12.
-- Their domains are disjoint and cover every admissible N, so a case split plus max of the two
-- thresholds recovers the frozen statement; neither premise alone implies it.

theorem Conjectures.Cuts.Cut8dee2f930d12a73e44d5076c
    (h₁ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → N ≤ (10:ℕ)^12 → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ, N = p + q + ∑ i : Fin 5, 2 ^ (a i + 1))
    (h₂ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (10:ℕ)^12 < N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ, N = p + q + ∑ i : Fin 5, 2 ^ (a i + 1)) :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ, N = p + q + ∑ i : Fin 5, 2 ^ (a i + 1)) := by
  try dsimp only
  obtain ⟨N₁, b₁⟩ := h₁
  obtain ⟨N₂, b₂⟩ := h₂
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  by_cases h : N ≤ (10:ℕ)^12
  · exact b₁ N (le_trans (le_max_left _ _) hN) h
  · exact b₂ N (le_trans (le_max_right _ _) hN) (by omega)
