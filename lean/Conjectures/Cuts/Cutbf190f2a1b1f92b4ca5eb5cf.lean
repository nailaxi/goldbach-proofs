import Mathlib

-- Cut of L-goldbach-binary-shift-central-hit.
-- child 1 zh: 初段 n ≤ 10^12 上的中心窗移位命中（无阈值，纯有限范围验证）。
-- child 1 en: Central-window shifted hit on the initial segment n <= 10^12, with no threshold (finite-range verification only).
-- child 2 zh: 尾段 n > 10^12 上的同一命中，仍保留阈值 N：解析输入要覆盖的范围。
-- child 2 en: The same hit on the tail n > 10^12, still with a threshold N: the range the analytic input must cover.
-- The frozen statement asks for one threshold covering every admissible integer. The first premise covers the
-- finite range n <= (10:ℕ)^12 with no threshold at all, the second covers the tail n > (10:ℕ)^12; together a case
-- split on n <= (10:ℕ)^12 recovers the frozen statement, and neither premise alone does.

theorem Conjectures.Cuts.Cutbf190f2a1b1f92b4ca5eb5cf
    (h₁ : ∀ n : ℕ, n ≤ (10:ℕ)^12 → Even n → ∃ e p q : ℕ, 1 ≤ e ∧ (2^e)^2 ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+2^e ∧ p+q ≤ 3*p ∧ 3*p ≤ 2*(p+q))
    (h₂ : ∃ N : ℕ, ∀ n ≥ N, (10:ℕ)^12 < n → Even n → ∃ e p q : ℕ, 1 ≤ e ∧ (2^e)^2 ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+2^e ∧ p+q ≤ 3*p ∧ 3*p ≤ 2*(p+q)) :
    (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ e p q : ℕ, 1 ≤ e ∧ (2^e)^2 ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+2^e ∧ p+q ≤ 3*p ∧ 3*p ≤ 2*(p+q)) := by
  obtain ⟨N, hN⟩ := h₂
  refine ⟨N, ?_⟩
  intro n hn
  by_cases h : n ≤ (10:ℕ)^12
  · exact h₁ n h
  · exact hN n hn (by omega)
