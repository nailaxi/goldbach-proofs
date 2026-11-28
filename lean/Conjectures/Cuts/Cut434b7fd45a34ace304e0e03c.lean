import Mathlib

-- Cut of L-goldbach-exception-four-sevenths-negative-energy.
-- child 1 zh: 冻结陈述在初段 X ≤ 10^12 上的受限版本（有限区间，可由数值/有限核验处理）。
-- child 1 en: The frozen statement restricted to the initial segment X <= 10^12 (finite-range verification).
-- child 2 zh: 冻结陈述在尾段 X > 10^12 上的受限版本（解析估计真正起作用的部分）。
-- child 2 en: The frozen statement restricted to the tail X > 10^12 (where the analytic estimate actually acts).
-- Both premises keep the same negative-part weight (max 0 (−minor n))^2; together they cover every X by a
-- case split, and the two constants are combined as C₁ + C₂, so the split is a genuine reduction of the
-- single asymptotic claim into a finite-range check plus a tail estimate.

theorem Conjectures.Cuts.Cut434b7fd45a34ace304e0e03c
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → X ≤ (10:ℕ)^12 → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e))
    (h₂ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (10:ℕ)^12 < X → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) := by
  dsimp only
  intro e he
  obtain ⟨C₁, N₁, hC₁, b₁⟩ := h₁ e he
  obtain ⟨C₂, N₂, hC₂, b₂⟩ := h₂ e he
  refine ⟨C₁ + C₂, max N₁ N₂, by linarith, ?_⟩
  intro X hX
  have hp : (0:ℝ) ≤ (X:ℝ) ^ ((18:ℝ)/7 + e) := by positivity
  have hmono : C₁ ≤ C₁ + C₂ := by linarith
  have hC₂' : C₂ ≤ C₁ + C₂ := by linarith
  by_cases h : X ≤ (10:ℕ)^12
  · have b := b₁ X (le_trans (le_max_left _ _) hX) h
    have hm : C₁ * (X:ℝ) ^ ((18:ℝ)/7 + e) ≤ (C₁ + C₂) * (X:ℝ) ^ ((18:ℝ)/7 + e) :=
      mul_le_mul_of_nonneg_right hmono hp
    linarith
  · have b := b₂ X (le_trans (le_max_right _ _) hX) (by omega)
    have hm : C₂ * (X:ℝ) ^ ((18:ℝ)/7 + e) ≤ (C₁ + C₂) * (X:ℝ) ^ ((18:ℝ)/7 + e) :=
      mul_le_mul_of_nonneg_right hC₂' hp
    linarith
