import Mathlib

theorem PEqualNP.Outside.L_goldbach_kernel_resonance :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b)); ∀ N : ℕ, ∀ a : ℤ, K N (a:ℝ) = ((N+1:ℕ):ℂ) := by
  dsimp only
  intro N a
  have harmonic (k : ℕ) :
      Complex.exp (((2 * Real.pi * ((k : ℝ) * (a : ℝ)) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨(k : ℤ) * a, ?_⟩
    push_cast
    ring
  simp only [harmonic, Finset.sum_const, Finset.card_range, nsmul_one]
