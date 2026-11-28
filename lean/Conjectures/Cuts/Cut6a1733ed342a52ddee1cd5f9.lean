import Mathlib

-- Cut of L-goldbach-beaumont-three-target-window.
-- child 1 zh: 初段 n ≤ 10^12 上的三目标命中（无阈值，纯有限范围），可由有限计算/区间核验处理。
-- child 1 en: The three-target hit on the initial segment n <= 10^12 with no threshold (a pure finite-range statement).
-- child 2 zh: 尾段 n > 10^12 上的同一命中，仍允许阈值 N₀；这是解析部分真正要处理的范围。
-- child 2 en: The same hit on the tail n > 10^12, still with a threshold N₀: the range the analytic input must cover.
-- The frozen statement asks for one threshold covering all even n. The two premises cover the two ranges with
-- no overlap, so a case split on n <= 10^12 recovers the frozen statement; neither premise alone does, and the
-- finite-range premise carries no threshold, so it is not vacuous.

theorem Conjectures.Cuts.Cut6a1733ed342a52ddee1cd5f9
    (h₁ : ∀ n : ℕ, n ≤ (10:ℕ)^12 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3*p ≤ 2*n ∧ 2*n ≤ 6*p ∧ |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ 2)
    (h₂ : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (10:ℕ)^12 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3*p ≤ 2*n ∧ 2*n ≤ 6*p ∧ |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ 2) :
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3*p ≤ 2*n ∧ 2*n ≤ 6*p ∧ |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ 2) := by
  obtain ⟨N, hN⟩ := h₂
  refine ⟨N, ?_⟩
  intro n hn hev
  by_cases h : n ≤ (10:ℕ)^12
  · exact h₁ n h hev
  · exact hN n hn (by omega) hev
