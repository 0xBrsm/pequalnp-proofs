import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2498_2 :
    (∀ (n : ℕ) (v : Fin n) (C : Circuit) (j : Fin C.gates.length), FanInTwo C →
      (let g := C.gates.get j
       g.inputs.head? == some v.val || g.op.eval [true, true] && g.inputs.contains v.val) = true →
      (∃ b : Bool, ∀ x : Fin n → Bool, x v = false →
        (C.wires (List.ofFn x)).getD (n+j.val) false = b) ∨
      ∃ w < n+j.val, ∀ x : Fin n → Bool, x v = false →
        (C.wires (List.ofFn x)).getD (n+j.val) false = (C.wires (List.ofFn x)).getD w false) →
    (∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      (let reads := fun i : Nat => D.gates.countP (fun g =>
         g.inputs.head? == some i || g.op.eval [true, true] && g.inputs.contains i)
       reads 0 ≤ 2 ∧ reads 1 ≤ 2 ∧ ∀ i ∈ [2,3,5,8], reads i ≤ 3) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) ≠
        (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit (tableIndex x)) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro reader search C fan first correct thin
  let F := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  have truth : ∀ x : Fin 9 → Bool, F x = (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit (tableIndex x) := by decide +kernel
  change circuitFun 9 C = F at correct
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil =>
    have h := first (fun _ => true)
    exact False.elim (by contradiction)
  | cons g gs =>
    let C : Circuit := ⟨g :: gs,out⟩
    let D : Circuit := ⟨gs,out⟩
    change FanInTwo C at fan
    change ∀ x, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1) at first
    change circuitFun 9 C = F at correct
    let step := fun (w : List Bool) (q : Gate) =>
      w ++ [q.op.eval (q.inputs.map fun i => w.getD i false)]
    have keep (qs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (qs.foldl step w).getD i false = w.getD i false := by
      induction qs generalizing w with
      | nil => rfl
      | cons q qs ih =>
        rw [List.foldl_cons, ih]
        · exact List.getD_append _ _ _ _ hi
        · simp [step]; omega
    have input (x : Fin 9 → Bool) (i : Fin 9) :
        (C.wires (List.ofFn x)).getD i.val false = x i := by
      change (C.gates.foldl step _).getD _ _ = _
      rw [keep _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      simp only [List.getElem_ofFn]
    let val := fun x : Fin 9 → Bool => g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
    have seed (x) : val x = (x 0 || x 1) := by
      have h := first x
      change (gs.foldl step (List.ofFn x ++ [val x])).getD 9 false = _ at h
      rw [keep _ _ _ (by simp only [List.length_append,List.length_ofFn,List.length_cons,List.length_nil]; decide)] at h
      exact h
    by_contra short
    have sz : D.size ≤ 14 := by
      change ¬16 ≤ (g::gs).length at short
      simp only [List.length_cons] at short
      change gs.length ≤ 14
      omega
    let pred := fun (v : ℕ) (q : Gate) =>
      q.inputs.head? == some v || q.op.eval [true,true] && q.inputs.contains v
    let reads := fun v => gs.countP (pred v)
    have counts (v : Fin 9) (hv : v ∈ ([0,1,2,3,5,8] : List (Fin 9))) :
        reads v.val ≤ 3 ∧ ((v = 0 ∨ v = 1) → reads v.val ≤ 2) := by
      let I := Finset.univ.filter (fun i : Fin gs.length => pred v.val (gs.get i) = true)
      let T := I.image (fun i => i.val + 1)
      have inj : Function.Injective (fun i : Fin gs.length => i.val + 1) :=
        fun a b h => Fin.ext (Nat.succ.inj h)
      have cardT : T.card = reads v.val := by
        rw [show T.card = I.card from Finset.card_image_of_injective _ inj]
        have h := List.countP_ofFn gs.get (pred v.val)
        rw [List.ofFn_get] at h
        exact h.symm
      let good := fun k : ℕ => k < C.size ∧
        ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → (C.wires (List.ofFn x)).getD (9+k) false = b) ∨
        ∃ w < 9+k, ∀ x : Fin 9 → Bool, x v = false →
          (C.wires (List.ofFn x)).getD (9+k) false = (C.wires (List.ofFn x)).getD w false)
      have each : ∀ k ∈ T, good k := by
        intro k hk
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
        have hl : i.val + 1 < C.gates.length := Nat.succ_lt_succ i.isLt
        exact ⟨hl, reader 9 v C ⟨_,hl⟩ fan (Finset.mem_filter.mp hi).2⟩
      constructor
      · rw [← cardT]
        exact thin v hv T each
      · intro hv01
        have zero : good 0 := by
          refine ⟨Nat.zero_lt_succ _, Or.inr ?_⟩
          rcases hv01 with rfl|rfl
          · refine ⟨(1 : Fin 9).val,by decide,fun x hx => ?_⟩
            simpa only [Nat.add_zero,first,hx,Bool.false_or] using (input x 1).symm
          · refine ⟨(0 : Fin 9).val,by decide,fun x hx => ?_⟩
            simpa only [Nat.add_zero,first,hx,Bool.or_false] using (input x 0).symm
        have h := thin v hv (insert 0 T) (fun k hk => by
          rcases Finset.mem_insert.mp hk with rfl|ht
          · exact zero
          · exact each k ht)
        have hn : 0 ∉ T := by simp [T]
        rw [Finset.card_insert_of_notMem hn,cardT] at h
        omega
    have hD : FanInTwo D := fun q hq => fan q (List.mem_cons_of_mem _ hq)
    obtain ⟨x,hx⟩ := search D hD sz (by
      change reads 0 ≤ 2 ∧ reads 1 ≤ 2 ∧ _
      refine ⟨(counts 0 (by decide)).2 (Or.inl rfl), (counts 1 (by decide)).2 (Or.inr rfl), ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      · exact (counts 2 (by decide)).1
      · exact (counts 3 (by decide)).1
      · exact (counts 5 (by decide)).1
      · exact (counts 8 (by decide)).1)
    apply hx
    rw [← seed, ← truth]
    exact congrFun correct x
