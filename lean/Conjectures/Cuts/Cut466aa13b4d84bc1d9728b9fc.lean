import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- The weighted Moebius sum is split along the two von Mangoldt branches it is made
-- of: the prime-power branch (Lambda n times log n) and the divisor branch
-- (the convolution of Lambda with Lambda).  Each branch is bounded above at every
-- cutoff, and the two bounds add.  The divisor branch is the open premise recorded
-- for this route by the earlier cut of eab152a8, so this decomposition exposes the
-- remaining prime-power branch separately.
-- Source: research/twin-primes.md (TP-0039: the long divisors keep the sign of
-- mu(d) against the primality of the cofactor).
-- child 1 zh: 素幂分支的加权 Möbius 和逐截点有上界。
-- child 1 en: The weighted Moebius sum of the prime-power branch is bounded above at every cutoff.
-- child 2 zh: 除数分支的加权 Möbius 和逐截点有上界。
-- child 2 en: The weighted Moebius sum of the divisor branch is bounded above at every cutoff.

theorem Conjectures.Cuts.Cut466aa13b4d84bc1d9728b9fc
    (h₁ : ∃ (C₁ : ℝ), (0 : ℝ) < C₁ ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ C₁ * ↑x2)
    (h₂ : ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ x1 * ↑x2)
    : ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ x1 * ↑x2 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro X
  have hid : (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)))
      = (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) + (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hid]
  have h1 := hb₁ X
  have h2 := hb₂ X
  nlinarith
