import Mathlib

-- Cut of L-goldbach-binary-shift-shared-exponent.
-- child 1 zh: 初段 n ≤ 10^12 上的相邻目标共用移位命中（无阈值，纯有限范围验证）。
-- child 1 en: Common-shift hit for adjacent targets on the initial segment n <= 10^12, with no threshold (finite-range verification only).
-- child 2 zh: 尾段 n > 10^12 上的同一命中，仍保留阈值 N：解析输入要覆盖的范围。
-- child 2 en: The same common-shift hit on the tail n > 10^12, still with a threshold N: the range the analytic input must cover.
-- The frozen statement asks for one threshold covering every admissible integer. The first premise covers the
-- finite range n <= (10:ℕ)^12 with no threshold at all, the second covers the tail n > (10:ℕ)^12; together a case
-- split on n <= (10:ℕ)^12 recovers the frozen statement, and neither premise alone does.

theorem Conjectures.Cuts.Cut6480120ab7b01d5c312ce0cb
    (h₁ : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∀ n : ℕ, n ≤ (10:ℕ)^12 → Even n → ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧ 0 < G (n-2^e) ∧ 0 < G (n+2-2^e))
    (h₂ : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ N : ℕ, ∀ n ≥ N, (10:ℕ)^12 < n → Even n → ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧ 0 < G (n-2^e) ∧ 0 < G (n+2-2^e)) :
    (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ N : ℕ, ∀ n ≥ N, Even n → ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧ 0 < G (n-2^e) ∧ 0 < G (n+2-2^e)) := by
  obtain ⟨N, hN⟩ := h₂
  refine ⟨N, ?_⟩
  intro n hn
  by_cases h : n ≤ (10:ℕ)^12
  · exact h₁ n h
  · exact hN n hn (by omega)
