import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- The weighted Moebius sum of the divisor branch is split into its two one-sided
-- halves: the two premises bound the sum from above and from below along every
-- cutoff, and their sum bounds the absolute value.  The sign of the Moebius weight
-- is the analytic content of the branch, so the two sides are attacked separately.
-- Source: research/twin-primes.md (long divisors: keep the sign of mu(d) against
-- the primality of the cofactor); the parent task is premise 1/2 of the cut of
-- L-twin-primes-cut-ee49891a8c82ba48c17ab308.
-- child 1 zh: 除数分支的加权 Möbius 和逐截点有上界。
-- child 1 en: The weighted Moebius sum of the divisor branch is bounded above at every cutoff.
-- child 2 zh: 除数分支的加权 Möbius 和逐截点有下界。
-- child 2 en: The weighted Moebius sum of the divisor branch is bounded below at every cutoff.

theorem Conjectures.Cuts.Cut3844de3d26dda07cf3c4dd88
    (h₁ : ∃ (C₁ : ℝ), (0 : ℝ) < C₁ ∧ ∀ (X : ℕ), (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ C₁ * ↑X)
    (h₂ : ∃ (C₂ : ℝ), (0 : ℝ) < C₂ ∧ ∀ (X : ℕ), -((∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ C₂ * ↑X)
    : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), |∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)| ≤ x1 * ↑x2) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro X
  have hX : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  rw [abs_le]
  constructor
  · have h := hb₂ X
    nlinarith
  · have h := hb₁ X
    nlinarith
