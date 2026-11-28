import Mathlib

-- Cut of L-goldbach-finite-minor-fixed-105-dstar.
-- child 1 zh: 冻结窗口 D* 中 n ≤ 10^19 的第一段有限子区间：给出同样的 −9/5·n 单侧实部下界。
-- child 1 en: First finite sub-range n <= 10^19 of the frozen window: same one-sided -9/5*n real-part floor.
-- child 2 zh: 冻结窗口 D* 中 n > 10^19 的第二段有限子区间：给出同样的 −9/5·n 单侧实部下界。
-- child 2 en: Second finite sub-range n > 10^19: same one-sided -9/5*n real-part floor. exp(exp(19/5)) < 10^20 so the two ranges cover D*.

theorem Conjectures.Cuts.Cutdab7dd37442db2c74d3b1fdf
    (h₁ : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (α : ℝ) => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*α); let arcs := fun (n : ℕ) => {t : ℝ | ∃ (q a : ℕ) (z : ℤ), 1≤q ∧ q≤105 ∧ a<q ∧ Nat.Coprime a q ∧ |t-((a:ℝ)/q+(z:ℝ))|≤105/((q:ℝ)*(n:ℝ))}; ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → n ≤ (10:ℕ)^19 → -(9/5:ℝ)*(n:ℝ) ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1 \ arcs n)) (fun t => (S n t)^2*E (-(n:ℝ)*t))).re)
    (h₂ : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (α : ℝ) => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*α); let arcs := fun (n : ℕ) => {t : ℝ | ∃ (q a : ℕ) (z : ℤ), 1≤q ∧ q≤105 ∧ a<q ∧ Nat.Coprime a q ∧ |t-((a:ℝ)/q+(z:ℝ))|≤105/((q:ℝ)*(n:ℝ))}; ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → (10:ℕ)^19 < n → -(9/5:ℝ)*(n:ℝ) ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1 \ arcs n)) (fun t => (S n t)^2*E (-(n:ℝ)*t))).re) :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (α : ℝ) => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*α); let arcs := fun (n : ℕ) => {t : ℝ | ∃ (q a : ℕ) (z : ℤ), 1≤q ∧ q≤105 ∧ a<q ∧ Nat.Coprime a q ∧ |t-((a:ℝ)/q+(z:ℝ))|≤105/((q:ℝ)*(n:ℝ))}; ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → -(9/5:ℝ)*(n:ℝ) ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1 \ arcs n)) (fun t => (S n t)^2*E (-(n:ℝ)*t))).re) := by
  dsimp only
  intro n hbig h30 hwin
  by_cases hsplit : n ≤ (10:ℕ)^19
  · exact h₁ n hbig h30 hwin hsplit
  · exact h₂ n hbig h30 hwin (by omega)
