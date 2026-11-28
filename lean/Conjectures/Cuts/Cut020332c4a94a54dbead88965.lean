import Mathlib

-- Cut of L-goldbach-dyn-ultrashort-restricted-hit.
-- child 1 zh: 初段 X ≤ 10^12 上的超短窗受限命中（无阈值，纯有限范围验证）。
-- child 1 en: Restricted hit in ultra-short windows on the initial segment X <= 10^12, with no threshold (finite-range verification only).
-- child 2 zh: 尾段 X > 10^12 上的同一命中，仍保留阈值 X₀：解析输入要覆盖的范围。
-- child 2 en: The same restricted hit on the tail X > 10^12, still with a threshold X0: the range the analytic input must cover.
-- The frozen statement asks for one threshold covering every admissible integer. The first premise covers the
-- finite range X <= (10:ℕ)^12 with no threshold at all, the second covers the tail X > (10:ℕ)^12; together a case
-- split on X <= (10:ℕ)^12 recovers the frozen statement, and neither premise alone does.

theorem Conjectures.Cuts.Cut020332c4a94a54dbead88965
    (h₁ : let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∀ X : ℕ, X ≤ (10:ℕ)^12 → ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n))
    (h₂ : let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∃ X₀ : ℕ, ∀ X ≥ X₀, (10:ℕ)^12 < X → ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) := by
  obtain ⟨N, hN⟩ := h₂
  refine ⟨N, ?_⟩
  intro X hn
  by_cases h : X ≤ (10:ℕ)^12
  · exact h₁ X h
  · exact hN X hn (by omega)
