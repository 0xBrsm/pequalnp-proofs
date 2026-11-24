import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1904_1
    (buildCover : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ x6.size ≤ x2.edgeFinset.card + x4.card - (1 : ℕ) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true)
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size)
    (account : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (K : Finset (Fin n)), NoFourCycle G → IsAO2 n C →
    circuitFun n C = graphFun G ∅ →
    IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n,
      e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set _)) K →
    G.edgeFinset.card + K.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n,
      e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1)
    (descend : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)),
  let repeated := fun (D : Circuit) => (G.edgeFinset.filter (fun e => ∃ u v : Fin n,
    e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n D (D.output - n) u v)).card
  (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G → IsMinCover G K →
  ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
    C.size + 1 < G.edgeFinset.card + K.card → 0 < repeated C →
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ repeated D < repeated C)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  intro n G inst htri hsquare
  have hfour : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap, hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq, hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (hsquare a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  let covers := Finset.univ.filter (fun T : Finset (Fin n) => G.IsVertexCover (T : Set (Fin n)))
  have hne : covers.Nonempty := by
    exact ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun {u v} _ => Or.inl (Finset.mem_univ u)⟩⟩
  obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image covers Finset.card hne
  have hcover : IsMinCover G K :=
    ⟨(Finset.mem_filter.mp hK).2, fun T hT => hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)⟩
  obtain ⟨B, hB, evalB, sizeB, safeB⟩ := buildCover n G K (fun _ _ h => hcover.1 h)
  refine ⟨B, hB, evalB, ?_, safeB⟩
  intro T hm heval
  by_contra! hsmall
  obtain ⟨C, hAO, hfun, hsize⟩ := normalize n G inst T hm (fun x => by rw [heval]; simp)
  let edges := fun (A : Circuit) => G.edgeFinset.filter (fun e => ∃ u v : Fin n,
    e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n A (A.output - n) u v)
  let fits := fun k => ∃ A : Circuit, IsAO2 n A ∧ circuitFun n A = graphFun G ∅ ∧
    A.size ≤ T.size ∧ (edges A).card = k
  have ex : ∃ k, fits k := ⟨_, C, hAO, hfun, hsize, rfl⟩
  obtain ⟨A, ao, computes, budget, ha⟩ := Nat.find_spec ex
  have cheap : A.size + 1 < G.edgeFinset.card + K.card := by omega
  by_cases zero : (edges A).card = 0
  · have hempty : edges A = ∅ := Finset.card_eq_zero.mp zero
    have deleted : G.deleteEdges (↑(edges A) : Set _) = G := by simp [hempty]
    have hc : IsMinCover (G.deleteEdges (↑(edges A) : Set _)) K := by rw [deleted]; exact hcover
    have cost := account n G A K hfour ao computes hc
    change G.edgeFinset.card + K.card ≤ A.size + (edges A).card + 1 at cost
    omega
  · obtain ⟨D, ado, fd, sz, lt⟩ := descend n G K htri hfour hcover A ao computes cheap (Nat.pos_of_ne_zero zero)
    have minimal := Nat.find_min' ex (show fits (edges D).card from ⟨D, ado, fd, sz.trans budget, rfl⟩)
    change (edges D).card < (edges A).card at lt
    omega
