import Mathlib

-- Cut of L-goldbach-fixed-shift-sextic-goldbach.
-- child 1 zh: 初段受限版本（变量≤ 10^12）：保留冻结阈值，仅限制到初始区间。
-- child 1 en: Initial-segment restriction (variable <= 10^12): keeps the frozen threshold, only restricts the range.
-- child 2 zh: 尾段受限版本（变量 > 10^12）：保留冻结阈值，只处理尾部区间。
-- child 2 en: Tail restriction (variable > 10^12): keeps the frozen threshold and covers only the tail range.
-- Both premises keep the frozen existential threshold and restrict the variable to one side of (10:ℕ)^12.
-- Their domains are disjoint and cover every admissible n, so a case split plus max of the two
-- thresholds recovers the frozen statement; neither premise alone implies it.

theorem Conjectures.Cuts.Cut6235b8d55679d70b47db7e34
    (h₁ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ≤ (10:ℕ)^12 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6)
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (10:ℕ)^12 < n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6) := by
  try dsimp only
  obtain ⟨N₁, b₁⟩ := h₁
  obtain ⟨N₂, b₂⟩ := h₂
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  by_cases h : n ≤ (10:ℕ)^12
  · exact b₁ n (le_trans (le_max_left _ _) hn) h
  · exact b₂ n (le_trans (le_max_right _ _) hn) (by omega)
