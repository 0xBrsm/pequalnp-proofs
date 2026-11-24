import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3634_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size) →
    (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.gates.length), PEqualNP.MetaComplexity.FanInTwo x2 → x2.output ≠ x1 + ↑x3 → (∀ (x6 : Fin x2.gates.length), ↑x3 < ↑x6 → x1 + ↑x3 ∉ if (x2.gates.get x6).op.eval [Bool.true, Bool.true] = Bool.true then (x2.gates.get x6).inputs else List.take (1 : ℕ) (x2.gates.get x6).inputs) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size < x2.size ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8 ++ [Bool.false]) = x2.eval (List.ofFn x8)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (13 : ℕ) → x1.output = (23 : ℕ) → x2 < x3 → x2 ≠ (0 : Fin (9 : ℕ)) ∧ x2 ≠ (4 : Fin (9 : ℕ)) → x3 ≠ (0 : Fin (9 : ℕ)) ∧ x3 ≠ (4 : Fin (9 : ℕ)) → (∀ x10 < (23 : ℕ), ∃ (x12 : Fin x1.gates.length), x10 < (11 : ℕ) + ↑x12 ∧ x10 ∈ if (x1.gates.get x12).op.eval [Bool.true, Bool.true] = Bool.true then (x1.gates.get x12).inputs else List.take (1 : ℕ) (x1.gates.get x12).inputs) → ∃ (x11 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x2 || x11 x3]) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro lb erase search C T fan card _ dis sz correct
  obtain ⟨a,b,hab,ht⟩ := Finset.card_eq_two.mp card
  obtain ⟨a,b,hab,ht⟩ : ∃ a b : Fin 9, a < b ∧ T = {a,b} := by
    rcases lt_or_gt_of_ne hab with h|h
    · exact ⟨a,b,h,ht⟩
    · exact ⟨b,a,h,ht.trans (Finset.pair_comm _ _)⟩
  rw [ht] at dis correct
  have ha : a ∉ ({0,4} : Finset (Fin 9)) := fun h => Finset.disjoint_left.mp dis (by simp) h
  have hb : b ∉ ({0,4} : Finset (Fin 9)) := fun h => Finset.disjoint_left.mp dis (by simp) h
  let F := fun x : Fin 9 → Bool => ([(1:ℕ),12,23,34,40,5,16,27,38,57,68,85]).any (fun d => x (Fin.ofNat 9 (d / 10)) && x (Fin.ofNat 9 (d % 10)))
  let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4,x a || x b]
  have calcF (x : Fin 9 → Bool) : C.eval (W x) = F x := by
    have eqseed : decide (∃ i ∈ ({a,b} : Finset (Fin 9)), x i = true) = (x a || x b) := by
      simp
    have h := correct x
    rw [eqseed] at h
    refine h.trans ?_
    dsimp [F]
    ac_rfl
  let g₀ : Gate := ⟨.or,[0,4]⟩
  let g₁ : Gate := ⟨.or,[a.val,b.val]⟩
  let P : Circuit := ⟨g₀ :: g₁ :: C.gates,C.output⟩
  have pf : FanInTwo P := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),Nat.le_refl 2⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),Nat.le_refl 2⟩
    exact fan g hg
  have psz : P.size = 15 := by
    change C.gates.length + 1 + 1 = 15
    change C.gates.length = 13 at sz
    omega
  have pe (x : Fin 9 → Bool) : P.eval (List.ofFn x) = F x := by
    have get (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt)]
      simp only [List.getElem_ofFn]
    let base := List.ofFn x
    have ext (v : Bool) (i : Fin 9) : (base ++ [v]).getD i.val false = x i :=
      (List.getD_append _ _ _ _ (by simp only [base,List.length_ofFn]; exact i.isLt)).trans (get i)
    change C.eval ((base ++ [([0,4] : List Nat).any (fun i => base.getD i false)]) ++
      [([a.val,b.val] : List Nat).any (fun i => (base ++ [([0,4] : List Nat).any (fun i => base.getD i false)]).getD i false)]) = _
    simp only [List.any_cons,List.any_nil,Bool.or_false,ext]
    rw [show base.getD 0 false = x 0 from get 0,show base.getD 4 false = x 4 from get 4]
    exact calcF x
  let used := fun (g : Gate) => if g.op.eval [true,true] then g.inputs else g.inputs.take 1
  have live (k : Fin P.gates.length) (hk : P.output ≠ 9+k.val) :
      ∃ j : Fin P.gates.length, k.val < j.val ∧ 9+k.val ∈ used (P.gates.get j) := by
    by_contra! h
    obtain ⟨D,df,ds,de⟩ := erase 9 P k pf hk h
    have bound := lb D df (fun x => by
      rw [de,pe]
      dsimp [F]
      ac_rfl)
    omega
  have out : C.output = 23 := by
    by_contra h
    have l : 14 < P.gates.length := by change 14 < P.size; omega
    obtain ⟨j,hj,_⟩ := live ⟨14,l⟩ h
    have jbound := j.isLt
    change j.val < P.size at jbound
    change 14 < j.val at hj
    omega
  suffices hall : ∀ w < 23, ∃ j : Fin C.gates.length, w < 11+j.val ∧ w ∈ used (C.gates.get j) by
    obtain ⟨x,hx⟩ := search C a b fan sz out hab (by simpa using ha) (by simpa using hb) hall
    exact hx (calcF x)
  intro w hw
  by_cases raw : w < 9
  · let i : Fin 9 := ⟨w,raw⟩
    let base := fun (a b i c j : Fin 9) => decide (j ≠ i ∧
      (j = c ∨ ((i=0 ∨ i=4) ∧ (j=0 ∨ j=4)) ∨ ((i=a ∨ i=b) ∧ (j=a ∨ j=b))))
    let flip := fun (a b i c j : Fin 9) => decide (j=i) || base a b i c j
    have witnesses : ∀ a b i : Fin 9, a < b → a ∉ ({0,4} : Finset (Fin 9)) →
        b ∉ ({0,4} : Finset (Fin 9)) → ∃ c : Fin 9,
        let x := flip a b i c
        let y := base a b i c
        F x ≠ F y ∧ (x 0 || x 4) = (y 0 || y 4) ∧ (x a || x b) = (y a || y b) := by decide +kernel
    obtain ⟨c,hf,hs,ht⟩ := witnesses a b i hab ha hb
    let x := flip a b i c
    let y := base a b i c
    by_contra! absent
    have unused (g) (hg : g ∈ C.gates) : w ∉ used g := by
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      exact hj ▸ absent j (by omega)
    let step := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map fun t => v.getD t false)]
    have same (gs : List Gate) (no : ∀ g ∈ gs,w ∉ used g) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
        (u v : List Bool) (len : u.length=v.length) (diff : ∀ t, t ≠ w → u.getD t false = v.getD t false) :
        ∀ t, t ≠ w → (gs.foldl step u).getD t false = (gs.foldl step v).getD t false := by
      induction gs generalizing u v with
      | nil => exact diff
      | cons g gs ih =>
        have no' := no g List.mem_cons_self
        have valEq : g.op.eval (g.inputs.map fun t => u.getD t false) = g.op.eval (g.inputs.map fun t => v.getD t false) := by
          rcases ops g List.mem_cons_self with hop|hop|hop
          · have eu : used g = g.inputs := by dsimp only [used]; rw [hop]; rfl
            rw [eu] at no'
            rw [show g.inputs.map (fun t => u.getD t false) = g.inputs.map (fun t => v.getD t false) from
                  List.map_congr_left (fun t ht => diff t (fun he => no' (he ▸ ht)))]
          · have eu : used g = g.inputs := by dsimp only [used]; rw [hop]; rfl
            rw [eu] at no'
            rw [show g.inputs.map (fun t => u.getD t false) = g.inputs.map (fun t => v.getD t false) from
                  List.map_congr_left (fun t ht => diff t (fun he => no' (he ▸ ht)))]
          · cases hi : g.inputs with
            | nil => rfl
            | cons h l =>
              have eu : used g = [h] := by dsimp only [used]; rw [hop,hi]; rfl
              rw [eu] at no'
              have hn : h ≠ w := fun he => no' (by simp [he])
              rw [hop]
              exact congrArg Bool.not (diff h hn)
        apply ih (fun q h => no q (List.mem_cons_of_mem _ h)) (fun q h => ops q (List.mem_cons_of_mem _ h))
        · simp [step,len]
        · intro t ht
          by_cases h : t < u.length
          · exact (List.getD_append _ _ _ _ h).trans ((diff t ht).trans (List.getD_append _ _ _ _ (len ▸ h)).symm)
          · dsimp only [step]
            rw [valEq]
            simp only [List.getD_eq_getElem?_getD,List.getElem?_append,len,ite_eq_right (show ¬t<v.length by omega)]
    apply hf
    change F x = F y
    rw [← calcF,← calcF]
    apply same C.gates unused (fun g hg => (fan g hg).1) (W x) (W y) (by simp [W])
    · intro t ht'
      by_cases h : t < 9
      · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_append _ _ _ _ (by simpa using h)]
        rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn,x,y,flip,show (⟨t,h⟩ : Fin 9) ≠ i from fun he => ht' (congrArg Fin.val he),decide_false,Bool.false_or]
      · simp only [W,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_right h]
        rw [show (x 0 || x 4) = (y 0 || y 4) from hs,show (x a || x b) = (y a || y b) from ht]
    · rw [out]; omega

  · let k : Fin P.gates.length := ⟨w-9,by change w-9 < P.size; omega⟩
    have ek : 9+k.val = w := by dsimp [k]; omega
    have hk : P.output ≠ 9+k.val := by change C.output ≠ _; rw [out,ek]; omega
    obtain ⟨j,hj,hm⟩ := live k hk
    rw [ek] at hm
    have later : 2 ≤ j.val := by
      by_contra! hj'
      have hj1 : j.val = 1 := by omega
      have get1 : P.gates.get j = g₁ := by
        have lt1 : 1 < P.gates.length := by change 1 < P.size; omega
        rw [show j = ⟨1,lt1⟩ from Fin.ext hj1]; rfl
      rw [get1] at hm
      change w ∈ [a.val,b.val] at hm
      have mem : w = a.val ∨ w = b.val := by simpa using hm
      rcases mem with rfl|rfl <;> exact raw (by apply Fin.isLt)
    let t : Fin C.gates.length := ⟨j.val-2,by have h := j.isLt; change j.val < C.gates.length+1+1 at h; omega⟩
    have et : j.val = t.val+2 := by dsimp [t]; omega
    have gett : P.gates.get j = C.gates.get t := by
      rw [show j = ⟨t.val+2,by omega⟩ from Fin.ext et]
      rfl
    exact ⟨t,by change w-9 < j.val at hj; omega,gett ▸ hm⟩
