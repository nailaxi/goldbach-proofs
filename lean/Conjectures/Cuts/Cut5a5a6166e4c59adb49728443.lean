import Mathlib

-- Cut of L-goldbach-fixed-ap-bmor-psi.
-- child 1 zh: 小模数范围 3 ≤ q ≤ 30 的 BMOR ψ 估计（有限多个模数，可用显式零点表/有限核验）。
-- child 1 en: BMOR psi estimate in the small-modulus range 3 <= q <= 30 (finitely many moduli, explicit zero tables).
-- child 2 zh: 较大模数范围 31 ≤ q ≤ 105 的同一估计（模数增大后 φ(q) 与误差项的比值更好控制）。
-- child 2 en: The same estimate for the larger moduli 31 <= q <= 105, where the totient-to-modulus ratio is more favourable.
-- Neither restricted estimate alone gives the frozen statement (which must hold for all 3 <= q <= 105);
-- the two constants and error terms are kept identical, so the case split on q <= 30 is a genuine reduction
-- of the published small-modulus bound into two independent modulus ranges.

theorem Conjectures.Cuts.Cut5a5a6166e4c59adb49728443
    (h₁ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → q ≤ 30 → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ)))
    (h₂ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → 30 < q → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) := by
  intro q a n h3 h105 ha hcop hn
  by_cases h : q ≤ 30
  · exact h₁ q a n h3 h105 h ha hcop hn
  · exact h₂ q a n h3 h105 (by omega) ha hcop hn
