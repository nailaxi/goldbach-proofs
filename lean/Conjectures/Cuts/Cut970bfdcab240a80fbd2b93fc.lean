import Mathlib

-- Cut of L-goldbach-dyadic-exception-little-o-sqrt.
-- child 1 zh: 初段 X ≤ 10^12 上的 o(√X) 例外集界（无阈值，纯有限范围验证）。
-- child 1 en: The o(sqrt X) exceptional-set bound on the initial segment X <= 10^12 (finite-range verification, no threshold).
-- child 2 zh: 尾段 X > 10^12 上的同一界，保留阈值 X₀：解析估计真正起作用的部分。
-- child 2 en: The same bound on the tail X > 10^12, keeping the threshold X0: the range the analytic input has to cover.
-- Neither premise alone gives the frozen statement; for each eps the two thresholds are combined with max, and a
-- case split on X <= 10^12 closes it, so this is a genuine reduction into two independent ranges.

theorem Conjectures.Cuts.Cut970bfdcab240a80fbd2b93fc
    (h₁ : let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → X ≤ (10:ℕ)^12 → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc X (2*X))).card : ℝ) ≤ ε * Real.sqrt (X : ℝ))
    (h₂ : let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (10:ℕ)^12 < X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc X (2*X))).card : ℝ) ≤ ε * Real.sqrt (X : ℝ)) :
    (let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc X (2*X))).card : ℝ) ≤ ε * Real.sqrt (X : ℝ)) := by
  dsimp only
  intro e he
  obtain ⟨N₁, b₁⟩ := h₁ e he
  obtain ⟨N₂, b₂⟩ := h₂ e he
  refine ⟨max N₁ N₂, ?_⟩
  intro X hX
  by_cases h : X ≤ (10:ℕ)^12
  · exact b₁ X (le_trans (le_max_left _ _) hX) h
  · exact b₂ X (le_trans (le_max_right _ _) hX) (by omega)
