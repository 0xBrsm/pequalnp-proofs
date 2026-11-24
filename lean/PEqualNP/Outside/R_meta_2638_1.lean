import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2638_1 :
    (∀ (x1 x2 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x4 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x2 → (∃ (x6 : Fin x1 → Bool), x3 (Function.update x6 x4 Bool.false) ≠ x3 (Function.update x6 x4 Bool.true)) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x3 (Function.update x7 x4 Bool.false) ≠ x3 (Function.update x8 x4 Bool.false)) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x3 (Function.update x8 x4 Bool.false)) (x2 - (1 : ℕ))) →
    (∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (z : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ i j, G.Adj i j → (G.neighborSet i).ncard = 3) →
      (∀ (i : Fin n) (p : G.Walk i i), p.IsCycle → 7 ≤ p.length) →
      (G.neighborSet z).ncard = 3 →
      (∀ x, f x = true ↔ ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true) →
      (∀ T : Finset (Fin n), (∀ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      HasCircuitSize n f s → (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + k ≤ s+1) →
    ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  intro pin core n k s G A z f deg girth iso _ hz spec cover size
  let H := G.deleteEdges (G.incidenceSet z)
  have mz := deg z hz
  obtain ⟨u,hzu⟩ := Set.nonempty_of_ncard_ne_zero (s := G.neighborSet z) (by omega)
  change G.Adj z u at hzu
  have du := deg u (iso u z hzu.symm)
  obtain ⟨v,hv,hvz⟩ : ∃ v ∈ G.neighborSet u, v ≠ z := by
    by_contra! h
    have small : (G.neighborSet u).ncard ≤ 1 :=
      (Set.ncard_le_one_iff (G.neighborSet u).toFinite).2 (fun hi hj => (h _ hi).trans (h _ hj).symm)
    omega
  have uv : H.Adj u v := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hv,hzu.ne.symm,hvz⟩
  have skip (i j : Fin n) (hij : H.Adj i j) : i ∉ A := iso i j (SimpleGraph.deleteIncidenceSet_adj.mp hij).1
  let E := fun x : Fin n → Bool => ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true
  let S := fun (B : Finset (Fin n)) (g : (Fin n → Bool) → Bool) =>
    ∀ x, g x = true ↔ (∃ a ∈ B, x a = true) ∨ E x
  have charge (B : Finset (Fin n)) : B ⊆ A → ∀ (g : (Fin n → Bool) → Bool) (t : ℕ),
      S B g → HasCircuitSize n g t → B.card + H.edgeSet.ncard + k ≤ t+1 := by
    induction B using Finset.induction_on with
    | empty =>
      intro _ g t sg cg
      have eq (x) : g x = true ↔ E x := by simpa using sg x
      simpa only [Finset.card_empty,Nat.zero_add] using core n k t G z g (fun i j hij => deg i (iso i j hij)) girth mz eq cover cg
    | @insert a B fresh ih =>
      intro sub g t sg cg
      have aa : a ∈ A := sub (Finset.mem_insert_self _ _)
      have na (i j) (hij : H.Adj i j) : i ≠ a := fun hi => skip i j hij (hi ▸ aa)
      let off := fun x : Fin n → Bool => Function.update x a false
      let g' := fun x => g (off x)
      have sg' : S B g' := by
        intro x
        change g (Function.update x a false) = true ↔ _
        rw [sg]
        constructor
        · rintro (⟨w,hw,h⟩|⟨i,j,hij,hi,hj⟩)
          · rcases Finset.mem_insert.mp hw with rfl|hw
            · simp at h
            · have hwa : w ≠ a := fun e => fresh (e ▸ hw)
              exact Or.inl ⟨w,hw,by simpa [Function.update_of_ne hwa] using h⟩
          · exact Or.inr ⟨i,j,hij,by simpa [Function.update_of_ne (na i j hij)] using hi,
                                  by simpa [Function.update_of_ne (na j i hij.symm)] using hj⟩
        · rintro (⟨w,hw,h⟩|⟨i,j,hij,hi,hj⟩)
          · have hwa : w ≠ a := fun e => fresh (e ▸ hw)
            exact Or.inl ⟨w,Finset.mem_insert_of_mem hw,by simpa [Function.update_of_ne hwa] using h⟩
          · exact Or.inr ⟨i,j,hij,by simpa [Function.update_of_ne (na i j hij)] using hi,
                                  by simpa [Function.update_of_ne (na j i hij.symm)] using hj⟩
      let O := fun _ : Fin n => false
      let I := fun _ : Fin n => true
      have low : g' O = false := by
        apply Bool.eq_false_iff.mpr
        rintro h
        rcases (sg' O).mp h with ⟨i,_,hi⟩|⟨i,j,_,hi,_⟩ <;> contradiction
      have high : g' I = true := (sg' I).mpr (Or.inr ⟨u,v,uv,rfl,rfl⟩)
      have single : g (Function.update O a true) = true :=
        (sg _).mpr (Or.inl ⟨a,Finset.mem_insert_self _ _,Function.update_self ..⟩)
      have dep : g (Function.update O a false) ≠ g (Function.update O a true) := by
        change g' O ≠ _; rw [low,single]; decide
      have nc : g (Function.update O a false) ≠ g (Function.update I a false) := by
        change g' O ≠ g' I; rw [low,high]; decide
      have cg' := pin n t g a cg ⟨O,dep⟩ ⟨O,I,nc⟩
      have pos : 0 < t := by
        by_contra! ht
        obtain ⟨C,_,hsize,hev⟩ := cg
        have ng : C.gates = [] := List.length_eq_zero_iff.mp (by change C.gates.length ≤ t at hsize; omega)
        have run (x : Fin n → Bool) : g x = (List.ofFn x).getD C.output false := by
          rw [← hev]
          change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
          rw [ng]; rfl
        by_cases ok : C.output < n
        · let w : Fin n := ⟨C.output,ok⟩
          have val (x : Fin n → Bool) : g x = x w := by
            rw [run,List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using ok)]
            exact List.getElem_ofFn ..
          by_cases eq : w = a
          · apply nc; rw [val,val,eq,Function.update_self,Function.update_self]
          · apply dep; rw [val,val,Function.update_of_ne eq,Function.update_of_ne eq]
        · apply dep
          rw [run,run,List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using (Nat.le_of_not_gt ok)),
            List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using (Nat.le_of_not_gt ok))]
      have smaller := ih (fun i hi => sub (Finset.mem_insert_of_mem hi)) g' (t-1) sg' cg'
      rw [Finset.card_insert_of_notMem fresh]
      omega
  exact charge A (fun _ h => h) f s spec size
