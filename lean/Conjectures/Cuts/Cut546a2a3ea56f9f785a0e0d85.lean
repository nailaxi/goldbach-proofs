import Mathlib
import PEqualNP.Outside.L_twin_primes_sifted_correlation
import PEqualNP.Outside.L_twin_primes_cosine_plancherel
import PEqualNP.Outside.L_twin_primes_theta_error_budget
import Conjectures.TwinPrimes.WindowEndpointOverhang
import Conjectures.TwinPrimes.RoughWindowPrimeExtraction
import Conjectures.TwinPrimes.ShiftedCharacterJacobi
import Conjectures.TwinPrimes.PrimeWheelProgressionBudget
import Conjectures.TwinPrimes.WheelMarginalCounterexample

-- TP-0052R is split at the two bookkeeping steps of the zero-padded spectral route
-- (the cosine Plancherel identity and the nonnegativity of the gap-two correlation)
-- plus the arithmetic input that a window carries a nonzero gap-two correlation mass.
-- The identity is the verified community module for the cosine Plancherel formula
-- (see research/twin-primes.md: TP-0052 and TP-0054 are equivalent, because zero
-- padding removes wraparound, so the energy is positive exactly when the window
-- holds a twin pair).  The premises are assumed here; no extra assumption is added.
-- child 1 zh: 谱能量等于模数乘以差二相关和（余弦 Plancherel 恒等式）。
-- child 1 en: The spectral energy equals the modulus times the gap-two correlation sum (cosine Plancherel).
-- child 2 zh: 差二相关和逐窗非负。
-- child 2 en: The gap-two correlation sum is nonnegative in every window.
-- child 3 zh: 存在任意大的窗口，其差二相关和非零（算术输入）。
-- child 3 en: Arbitrarily large windows carry a nonzero gap-two correlation sum (the arithmetic input).

theorem Conjectures.Cuts.Cut546a2a3ea56f9f785a0e0d85
    (h₁ : ∀ X : ℕ, (letI : NeZero (2*X+5) := ⟨Nat.succ_ne_zero _⟩; (∑ k : ZMod (2*X+5), (ZMod.stdAddChar (N:=2*X+5) (2*k)).re * ‖ZMod.dft (fun j : ZMod (2*X+5) => (((if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) : ℝ) : ℂ)) k‖^2) = (2*X+5 : ℝ) * (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0))))
    (h₂ : ∀ X : ℕ, (letI : NeZero (2*X+5) := ⟨Nat.succ_ne_zero _⟩; 0 ≤ (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0))))
    (h₃ : ∀ B : ℕ, ∃ X : ℕ, B < X ∧ (letI : NeZero (2*X+5) := ⟨Nat.succ_ne_zero _⟩; (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0)) ≠ 0))
    : (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let N := fun (X : ℕ) => 2*X+5; let f := fun (X n : ℕ) => if n ∈ w X ∧ n.Prime then Real.log n else 0; let energy := fun (X : ℕ) => letI : NeZero (N X) := ⟨Nat.succ_ne_zero _⟩; ∑ k : ZMod (N X), (ZMod.stdAddChar (N:=N X) (2*k)).re * ‖ZMod.dft (fun j : ZMod (N X) => ((f X j.val:ℝ):ℂ)) k‖^2; ∀ B : ℕ, ∃ X : ℕ, B<X ∧ 0<energy X) := by
  simp only []
  intro B
  obtain ⟨X, hX, hne⟩ := h₃ B
  refine ⟨X, hX, ?_⟩
  have hE : (∑ k : ZMod (2*X+5), (ZMod.stdAddChar (N:=2*X+5) (2*k)).re * ‖ZMod.dft (fun j : ZMod (2*X+5) => (((if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) : ℝ) : ℂ)) k‖^2) = (2*X+5 : ℝ) * (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0)) := by
    simpa only [] using h₁ X
  have hnn : (0:ℝ) ≤ (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0)) := by
    simpa only [] using h₂ X
  have hc : (0:ℝ) < (∑ j : ZMod (2*X+5), (if (j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ j.val.Prime then Real.log (j.val : ℝ) else 0) * (if ((j+2).val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)) ∧ (j+2).val.Prime then Real.log ((j+2).val : ℝ) else 0)) := lt_of_le_of_ne hnn (Ne.symm hne)
  have hN : (0:ℝ) < (2*X+5 : ℝ) := by positivity
  exact lt_of_lt_of_eq (mul_pos hN hc) hE.symm
