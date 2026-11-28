import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56219 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (279137471 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [3, 7]⟩,
    ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [11, 6]⟩, ⟨.not, [12]⟩, ⟨.and, [5, 13]⟩,
    ⟨.or, [10, 14]⟩, ⟨.not, [15]⟩], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
