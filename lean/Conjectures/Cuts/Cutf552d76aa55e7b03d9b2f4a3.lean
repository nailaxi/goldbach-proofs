import Mathlib

-- Cut of L-goldbach-finite-weighted-sieve-two-factor-dstar.
-- child 1 zh: 冻结窗口 D* 中 n ≤ 10^19 的第一段：仍然存在给出正加权筛余量的参数 (z,y)。
-- child 1 en: First finite sub-range n <= 10^19 of D*: parameters (z,y) giving a positive weighted-sieve margin still exist.
-- child 2 zh: 冻结窗口 D* 中 n > 10^19 的第二段：仍然存在给出正加权筛余量的参数 (z,y)。
-- child 2 en: Second finite sub-range n > 10^19 of D*: same positive-margin parameters exist (D* ends below 10^20).

theorem Conjectures.Cuts.Cutf552d76aa55e7b03d9b2f4a3
    (h₁ : let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → n ≤ (10:ℕ)^19 → ∃ z y : ℕ, 2<z ∧ z<y ∧ n≤y^3 ∧ n≤z*y^2 ∧ 0<(∑ p ∈ Finset.filter (fun p => 2≤n-p) (A n z), W z y (n-p)))
    (h₂ : let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → (10:ℕ)^19 < n → ∃ z y : ℕ, 2<z ∧ z<y ∧ n≤y^3 ∧ n≤z*y^2 ∧ 0<(∑ p ∈ Finset.filter (fun p => 2≤n-p) (A n z), W z y (n-p))) :
    (let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → ∃ z y : ℕ, 2<z ∧ z<y ∧ n≤y^3 ∧ n≤z*y^2 ∧ 0<(∑ p ∈ Finset.filter (fun p => 2≤n-p) (A n z), W z y (n-p))) := by
  dsimp only
  intro n hbig h30 hwin
  by_cases hsplit : n ≤ (10:ℕ)^19
  · exact h₁ n hbig h30 hwin hsplit
  · exact h₂ n hbig h30 hwin (by omega)
