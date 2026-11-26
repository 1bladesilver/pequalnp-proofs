import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25325 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180507 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.not, [4]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
