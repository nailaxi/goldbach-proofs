import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- The divisor branch is cut at the same cube-root threshold the route uses for the
-- long divisors: the divisors d of n with d at most the cube root of the cutoff and
-- the remaining divisors are bounded separately, and the two bounds add.
-- Source: research/twin-primes.md (TP-0038 and TP-0039: split the divisors of p+2
-- at D = floor X^(1/3), the short side is a finite average, the long side has to
-- keep the sign of mu(d) against the primality of the cofactor).
-- child 1 zh: 截点立方根以内的短除数分支的加权和逐截点有上界。
-- child 1 en: The weighted sum of the short divisors, at most the cube root of the cutoff, is bounded at every cutoff.
-- child 2 zh: 截点立方根以外的长除数分支的加权和逐截点有上界。
-- child 2 en: The weighted sum of the remaining long divisors past the cube root of the cutoff is bounded at every cutoff.

theorem Conjectures.Cuts.Cutaedf5e9753bee8295314eeab
    (h₁ : ∃ (C₁ : ℝ), (0 : ℝ) < C₁ ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => x4 ≤ ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ C₁ * ↑x2)
    (h₂ : ∃ (C₂ : ℝ), (0 : ℝ) < C₂ ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => ¬ x4 ≤ ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ C₂ * ↑x2)
    : ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * x3.divisors.sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ x1 * ↑x2 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro X
  have hid : (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => x4 ≤ ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) + (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => ¬ x4 ≤ ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) = (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * x3.divisors.sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors)
      (p := fun d => d ≤ ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊)
      (f := fun d => ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d))]
    ring
  rw [← hid]
  calc (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => x4 ≤ ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) + (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (x3.divisors.filter (fun x4 => ¬ x4 ≤ ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊)).sum (fun x4 => ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤ C₁ * ↑X + C₂ * ↑X := add_le_add (hb₁ X) (hb₂ X)
    _ = (C₁ + C₂) * ↑X := by ring
