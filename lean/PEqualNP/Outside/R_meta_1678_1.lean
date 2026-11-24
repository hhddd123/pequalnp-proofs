import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-1678`: a case split on the second gate. Either the circuit has at most
one gate, or its second gate exists and is an AND, an OR, or a NOT. -/
theorem PEqualNP.Outside.R_meta_1678_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.size ≤ 1 → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → 16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) := by
  classical
  intro h1 h2 h3 h4 C hfan hfirst hfun
  by_cases hsmall : C.size ≤ 1
  · exact h1 C hfan hfirst hfun hsmall
  · have hlen : 1 < C.gates.length := by
      have hsz : C.size = C.gates.length := rfl
      omega
    obtain ⟨g, hg⟩ : ∃ g, C.gates[1]? = Option.some g := by
      cases h : C.gates[1]? with
      | none => exact absurd h (by simp [List.getElem?_eq_none_iff]; omega)
      | some g => exact ⟨g, rfl⟩
    have hmg : g ∈ C.gates := List.mem_of_getElem? hg
    have hmem : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simpa using (hfan g hmg).1
    rcases hmem with h | h | h
    · exact h2 C hfan hfirst hfun ⟨g, hg, h⟩
    · exact h3 C hfan hfirst hfun ⟨g, hg, h⟩
    · exact h4 C hfan hfirst hfun ⟨g, hg, h⟩
