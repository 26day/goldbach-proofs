import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_replacement_lone_linf :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); ∀ (u v : ℕ → ℝ) (n : ℕ) (M : ℝ), (∀ k≤n, |u k|≤M ∧ |v k|≤M) → |conv u u n-conv v v n| ≤ 2*M*Finset.sum (Finset.range (n+1)) (fun k => |u k-v k|) := by
  dsimp only
  intro u v n M hcap
  let err (k : ℕ) : ℝ := |u k - v k|
  have hterm (k : ℕ) (hk : k ≤ n) :
      |u k * u (n-k) - v k * v (n-k)| ≤ M * (err k + err (n-k)) := by
    have hsplit : u k * u (n-k) - v k * v (n-k) =
        v (n-k) * (u k - v k) + u k * (u (n-k) - v (n-k)) := by ring
    rw [hsplit, mul_add]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (hcap (n-k) (Nat.sub_le n k)).2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (hcap k hk).1 (abs_nonneg _))
  have hreflect : (∑ k ∈ Finset.range (n+1), err (n-k)) =
      ∑ k ∈ Finset.range (n+1), err k := by
    simpa using Finset.sum_range_reflect err (n+1)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), M * (err k + err (n-k)) := by
      exact Finset.sum_le_sum fun k hk => hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = 2 * M * (∑ k ∈ Finset.range (n+1), err k) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hreflect]
      ring
