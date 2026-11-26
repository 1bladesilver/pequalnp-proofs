import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25190 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18073 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [2, 0]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
