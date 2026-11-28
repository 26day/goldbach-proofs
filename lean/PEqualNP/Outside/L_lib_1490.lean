import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1490_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ValidPos (n : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs, i < n + j)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_length (w : List Bool) (gs : List Gate) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g t ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (d : α) {i : Nat} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD, List.getElem?_append_left hi]

lemma foldl_stepWire_prefix (w : List Bool) (gs : List Gate) {i : Nat} (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hi']
    exact getD_append_left w _ false hi

lemma foldl_stepWire_append (w : List Bool) (gs1 gs2 : List Gate) :
    (gs1 ++ gs2).foldl stepWire w = gs2.foldl stepWire (gs1.foldl stepWire w) :=
  List.foldl_append

lemma getD_singleton_last {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD]

lemma validPos_append {n : Nat} {gs1 gs2 : List Gate}
    (h1 : ValidPos n gs1) (h2 : ValidPos (n + gs1.length) gs2) :
    ValidPos n (gs1 ++ gs2) := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact h1.1 g hg1
    · exact h2.1 g hg2
  · intro j hj i hi
    by_cases hlt : j < gs1.length
    · have hget : (gs1 ++ gs2).getD j ⟨GateOp.and, []⟩ = gs1.getD j ⟨GateOp.and, []⟩ :=
        getD_append_left gs1 gs2 _ hlt
      rw [hget] at hi
      exact h1.2 j hlt i hi
    · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
      have hsub : j - gs1.length < gs2.length := by
        rw [List.length_append] at hj; omega
      have hget : (gs1 ++ gs2).getD j ⟨GateOp.and, []⟩ = gs2.getD (j - gs1.length) ⟨GateOp.and, []⟩ := by
        simp only [List.getD, List.getElem?_append_right hge]
      rw [hget] at hi
      have hb := h2.2 (j - gs1.length) hsub i hi
      omega

lemma validPos_to_pos {h : Nat} (D : Circuit) (hv : ValidPos (h + 2) D.gates)
    (hout : D.output < h + 2 + D.size) :
    FanInTwo D ∧ ReadsBack (h + 2) D ∧ D.output < h + 2 + D.size ∧
      PEqualNP.NotBracket.notCount D = 0 := by
  refine ⟨?_, ?_, hout, ?_⟩
  · intro g hg
    have h1 := hv.1 g hg
    refine ⟨?_, h1.2⟩
    rcases h1.1 with ho | ho <;> simp [ho]
  · intro j hj i hi
    have hgate : gateAt D j = D.gates.getD j ⟨GateOp.and, []⟩ := by
      simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hgate] at hi
    exact hv.2 j hj i hi
  · unfold PEqualNP.NotBracket.notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    have h1 := (hv.1 g hg).1
    rcases h1 with ho | ho <;> simp [ho]

lemma pos_to_validPos {h : Nat} (D : Circuit)
    (hfit : FanInTwo D) (hrb : ReadsBack (h + 2) D) (hnc : PEqualNP.NotBracket.notCount D = 0) :
    ValidPos (h + 2) D.gates := by
  constructor
  · intro g hg
    have h1 := hfit g hg
    have hnot : g.op ≠ GateOp.not := by
      intro hne
      unfold PEqualNP.NotBracket.notCount at hnc
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hnc
      have hbad := hnc g hg
      simp [hne] at hbad
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have hm := h1.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with ho | ho | ho
      · exact Or.inl ho
      · exact Or.inr ho
      · exact absurd ho hnot
    exact ⟨hop, h1.2⟩
  · intro j hj i hi
    have hgate : D.gates.getD j ⟨GateOp.and, []⟩ = gateAt D j := by
      simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hgate] at hi
    exact hrb j hj i hi

def chainAux (op : GateOp) (base : Nat) (cur : Nat) : List Nat → List Gate × Nat
  | [] => ([], cur)
  | w :: rest =>
    let r := chainAux op (base + 1) base rest
    (⟨op, [cur, w]⟩ :: r.1, r.2)

lemma chainAux_length (op : GateOp) (base cur : Nat) (ws : List Nat) :
    (chainAux op base cur ws).1.length = ws.length := by
  induction ws generalizing base cur with
  | nil => rfl
  | cons w rest ih => simp [chainAux, ih]

lemma chainAux_valid (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (base cur : Nat) (ws : List Nat)
    (hcur : cur < base) (hws : ∀ w ∈ ws, w < base) :
    ValidPos base (chainAux op base cur ws).1 ∧
    (chainAux op base cur ws).2 < base + ws.length := by
  induction ws generalizing base cur with
  | nil =>
    refine ⟨⟨by simp [chainAux], by simp [chainAux]⟩, ?_⟩
    simpa [chainAux] using hcur
  | cons w rest ih =>
    have hw : w < base := hws w (by simp)
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    have hih := ih (base + 1) base (Nat.lt_succ_self base) hrest
    constructor
    · constructor
      · intro g hg
        simp only [chainAux, List.mem_cons] at hg
        rcases hg with rfl | hgt
        · exact ⟨hop, by simp⟩
        · exact hih.1.1 g hgt
      · intro j hj i hi
        simp only [chainAux, List.length_cons] at hj
        cases j with
        | zero =>
          simp only [chainAux, List.getD, List.getElem?_cons_zero, Option.getD_some,
            List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact hcur
          · exact hw
        | succ j' =>
          simp only [chainAux, List.getD, List.getElem?_cons_succ] at hi
          have hb := hih.1.2 j' (by omega) i hi
          omega
    · simp only [chainAux, List.length_cons]
      have hb := hih.2
      omega

lemma chainAux_eval_or (base cur : Nat) (ws : List Nat) (w : List Bool)
    (hlen : w.length = base) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    ((chainAux GateOp.or base cur ws).1.foldl stepWire w).getD (chainAux GateOp.or base cur ws).2 false =
    (w.getD cur false || ws.any (fun u => w.getD u false)) := by
  induction ws generalizing base cur w with
  | nil => simp [chainAux]
  | cons a rest ih =>
    simp only [chainAux, List.foldl_cons, List.any_cons]
    let w1 := stepWire w ⟨GateOp.or, [cur, a]⟩
    have hlen1 : w1.length = base + 1 := by simp [w1, stepWire, hlen]
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    rw [ih (base + 1) base w1 hlen1 (Nat.lt_succ_self base) hrest]
    have hcur1 : w1.getD base false = (w.getD cur false || w.getD a false) := by
      have : w1 = w ++ [w.getD cur false || w.getD a false] := by
        simp [w1, stepWire, GateOp.eval]
      rw [this, ← hlen, getD_singleton_last]
    have hany : rest.any (fun u => w1.getD u false) = rest.any (fun u => w.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      exact exists_congr fun u => and_congr_right fun hu => by
        have hu' : u < w.length := hlen.symm ▸ hws u (by simp [hu])
        dsimp only [w1, stepWire]
        rw [getD_append_left w _ false hu']
    rw [hcur1, hany, Bool.or_assoc]

lemma chainAux_eval_and (base cur : Nat) (ws : List Nat) (w : List Bool)
    (hlen : w.length = base) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    ((chainAux GateOp.and base cur ws).1.foldl stepWire w).getD (chainAux GateOp.and base cur ws).2 false =
    (w.getD cur false && ws.all (fun u => w.getD u false)) := by
  induction ws generalizing base cur w with
  | nil => simp [chainAux]
  | cons a rest ih =>
    simp only [chainAux, List.foldl_cons, List.all_cons]
    let w1 := stepWire w ⟨GateOp.and, [cur, a]⟩
    have hlen1 : w1.length = base + 1 := by simp [w1, stepWire, hlen]
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    rw [ih (base + 1) base w1 hlen1 (Nat.lt_succ_self base) hrest]
    have hcur1 : w1.getD base false = (w.getD cur false && w.getD a false) := by
      have : w1 = w ++ [w.getD cur false && w.getD a false] := by
        simp [w1, stepWire, GateOp.eval]
      rw [this, ← hlen, getD_singleton_last]
    have hall : rest.all (fun u => w1.getD u false) = rest.all (fun u => w.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact forall_congr' fun u => imp_congr_right fun hu => by
        have hu' : u < w.length := hlen.symm ▸ hws u (by simp [hu])
        dsimp only [w1, stepWire]
        rw [getD_append_left w _ false hu']
    rw [hcur1, hall, Bool.and_assoc]

def orList (base falseW : Nat) : List Nat → List Gate × Nat
  | [] => ([], falseW)
  | a :: rest => chainAux GateOp.or base a rest

def andList (base trueW : Nat) : List Nat → List Gate × Nat
  | [] => ([], trueW)
  | a :: rest => chainAux GateOp.and base a rest

lemma orList_len (base falseW : Nat) (ws : List Nat) : (orList base falseW ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [orList]
  | cons a rest => simp [orList, chainAux_length]

lemma andList_len (base trueW : Nat) (ws : List Nat) : (andList base trueW ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [andList]
  | cons a rest => simp [andList, chainAux_length]

lemma orList_spec (base falseW : Nat) (ws : List Nat) (hf : falseW < base) (hws : ∀ u ∈ ws, u < base) :
    ValidPos base (orList base falseW ws).1 ∧
    (orList base falseW ws).2 < base + (orList base falseW ws).1.length ∧
    ∀ (w : List Bool), w.length = base → w.getD falseW false = false →
      ((orList base falseW ws).1.foldl stepWire w).getD (orList base falseW ws).2 false =
      ws.any (fun u => w.getD u false) := by
  cases ws with
  | nil =>
    refine ⟨⟨by simp [orList], by simp [orList]⟩, by simpa [orList] using hf, ?_⟩
    intro w _ hw; simpa [orList] using hw
  | cons a rest =>
    have hch := chainAux_valid GateOp.or (Or.inr rfl) base a rest (hws a (by simp))
      (fun u hu => hws u (by simp [hu]))
    refine ⟨hch.1, ?_, ?_⟩
    · simp only [orList, chainAux_length]; exact hch.2
    · intro w hlen _
      simp only [orList, List.any_cons]
      exact chainAux_eval_or base a rest w hlen (hws a (by simp)) (fun u hu => hws u (by simp [hu]))

lemma andList_spec (base trueW : Nat) (ws : List Nat) (ht : trueW < base) (hws : ∀ u ∈ ws, u < base) :
    ValidPos base (andList base trueW ws).1 ∧
    (andList base trueW ws).2 < base + (andList base trueW ws).1.length ∧
    ∀ (w : List Bool), w.length = base → w.getD trueW false = true →
      ((andList base trueW ws).1.foldl stepWire w).getD (andList base trueW ws).2 false =
      ws.all (fun u => w.getD u false) := by
  cases ws with
  | nil =>
    refine ⟨⟨by simp [andList], by simp [andList]⟩, by simpa [andList] using ht, ?_⟩
    intro w _ hw; simpa [andList] using hw
  | cons a rest =>
    have hch := chainAux_valid GateOp.and (Or.inl rfl) base a rest (hws a (by simp))
      (fun u hu => hws u (by simp [hu]))
    refine ⟨hch.1, ?_, ?_⟩
    · simp only [andList, chainAux_length]; exact hch.2
    · intro w hlen _
      simp only [andList, List.all_cons]
      exact chainAux_eval_and base a rest w hlen (hws a (by simp)) (fun u hu => hws u (by simp [hu]))

def remapWire (n_old base : Nat) (inpMap : Nat → Nat) (w : Nat) : Nat :=
  if w < n_old then inpMap w else base + (w - n_old)

def remapGates (n_old base : Nat) (inpMap : Nat → Nat) (gs : List Gate) : List Gate :=
  gs.map (fun g => ⟨g.op, g.inputs.map (remapWire n_old base inpMap)⟩)

lemma remapGates_valid {n_old base : Nat} {inpMap : Nat → Nat} {gs : List Gate}
    (hv : ValidPos n_old gs) (hmap : ∀ i < n_old, inpMap i < base) :
    ValidPos base (remapGates n_old base inpMap gs) := by
  constructor
  · intro g hg
    simp only [remapGates, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have h := hv.1 g0 hg0
    exact ⟨h.1, by simp [h.2]⟩
  · intro j hj i hi
    simp only [remapGates, List.length_map] at hj
    have hget : (remapGates n_old base inpMap gs).getD j ⟨GateOp.and, []⟩ =
        ⟨(gs.getD j ⟨GateOp.and, []⟩).op, (gs.getD j ⟨GateOp.and, []⟩).inputs.map (remapWire n_old base inpMap)⟩ := by
      simp only [remapGates, List.getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some]
    rw [hget] at hi
    simp only [List.mem_map] at hi
    obtain ⟨u, hu, rfl⟩ := hi
    have hb := hv.2 j hj u hu
    unfold remapWire
    split_ifs with hlt
    · exact Nat.lt_of_lt_of_le (hmap u hlt) (Nat.le_add_right base j)
    · omega

lemma remapGates_eval {n_old base : Nat} (inpMap : Nat → Nat) (gs : List Gate)
    (w_old w_new : List Bool)
    (ho : w_old.length = n_old) (hn : w_new.length = base)
    (hmap : ∀ i < n_old, inpMap i < base)
    (hagree : ∀ i < n_old, w_new.getD (inpMap i) false = w_old.getD i false) :
    ∀ u < n_old + gs.length,
      ((remapGates n_old base inpMap gs).foldl stepWire w_new).getD (remapWire n_old base inpMap u) false =
      (gs.foldl stepWire w_old).getD u false := by
  have hgen : ∀ (gs1 gs2 : List Gate),
      gs1 ++ gs2 = gs →
      ∀ u < n_old + gs1.length,
        ((remapGates n_old base inpMap gs1).foldl stepWire w_new).getD (remapWire n_old base inpMap u) false =
        (gs1.foldl stepWire w_old).getD u false := by
    intro gs1
    induction gs1 using List.reverseRecOn with
    | nil =>
      intro _ _ u hu
      simp only [remapGates, List.map_nil, List.foldl_nil, List.length_nil, Nat.add_zero] at hu ⊢
      unfold remapWire
      rw [if_pos hu]
      exact hagree u hu
    | append_singleton gs1 g ih =>
      intro gs2 hcat u hu
      have hih := ih (g :: gs2) (by simpa [List.append_assoc] using hcat)
      simp only [remapGates, List.map_append, List.map_singleton, foldl_stepWire_append,
        List.foldl_cons, List.foldl_nil]
      let wn1 := (remapGates n_old base inpMap gs1).foldl stepWire w_new
      let wo1 := gs1.foldl stepWire w_old
      have hwn1 : wn1.length = base + gs1.length := by
        simp [wn1, foldl_stepWire_length, hn, remapGates]
      have hwo1 : wo1.length = n_old + gs1.length := by
        simp [wo1, foldl_stepWire_length, ho]
      simp only [List.length_append, List.length_singleton] at hu
      by_cases hlt : u < n_old + gs1.length
      · have hrm : remapWire n_old base inpMap u < wn1.length := by
          rw [hwn1]; unfold remapWire
          split_ifs with hu0
          · exact Nat.lt_of_lt_of_le (hmap u hu0) (Nat.le_add_right _ _)
          · omega
        change (stepWire wn1 _).getD (remapWire n_old base inpMap u) false = (stepWire wo1 g).getD u false
        dsimp only [stepWire]
        rw [getD_append_left wn1 _ false hrm, getD_append_left wo1 _ false (by omega)]
        exact hih u hlt
      · have hueq : u = n_old + gs1.length := by omega
        subst hueq
        have hrm : remapWire n_old base inpMap (n_old + gs1.length) = wn1.length := by
          rw [hwn1]; unfold remapWire
          rw [if_neg (by omega)]
          omega
        change (stepWire wn1 _).getD (remapWire n_old base inpMap (n_old + gs1.length)) false =
          (stepWire wo1 g).getD (n_old + gs1.length) false
        rw [hrm]
        dsimp only [stepWire]
        rw [getD_singleton_last wn1, ← hwo1, getD_singleton_last wo1]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro v hv
        simp only [Function.comp_apply]
        by_cases hvb : v < n_old + gs1.length
        · exact hih v hvb
        · have hv_oob1 : wn1.length ≤ remapWire n_old base inpMap v := by
            rw [hwn1]; unfold remapWire; rw [if_neg (by omega)]; omega
          have hv_oob2 : wo1.length ≤ v := by omega
          simp [List.getD, List.getElem?_eq_none hv_oob1, List.getElem?_eq_none hv_oob2]
  exact hgen gs [] (List.append_nil gs)

lemma matching_of_cover_le2 {α : Type*} [DecidableEq α] {m : Nat}
    (S : α → Finset (Fin m)) (X : Finset α) (hle2 : ∀ x ∈ X, (S x).card ≤ 2) :
    ∃ M ⊆ X,
      (∀ x ∈ M, (S x).card = 2) ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → Disjoint (S x) (S y)) ∧
      (X.biUnion S).card ≤ X.card + M.card := by
  classical
  induction X using Finset.induction_on with
  | empty =>
    exact ⟨∅, Finset.Subset.rfl, by simp, by simp, by simp⟩
  | @insert x X hx ih =>
    have hle2' : ∀ y ∈ X, (S y).card ≤ 2 := fun y hy => hle2 y (Finset.mem_insert_of_mem hy)
    obtain ⟨M, hMX, hM2, hMdisj, hcard⟩ := ih hle2'
    let U := X.biUnion S
    have hcard_ins : (insert x X).card = X.card + 1 := Finset.card_insert_of_notMem hx
    have hbiu : (insert x X).biUnion S = S x ∪ U := Finset.biUnion_insert
    by_cases hdisj : (S x).card = 2 ∧ Disjoint (S x) U
    · refine ⟨insert x M, Finset.insert_subset_insert x hMX, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyM
        · exact hdisj.1
        · exact hM2 y hyM
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with rfl | hyM <;>
        rcases Finset.mem_insert.mp hz with rfl | hzM
        · exact absurd rfl hyz
        · exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S (hMX hzM)) hdisj.2
        · exact (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S (hMX hyM)) hdisj.2).symm
        · exact hMdisj y hyM z hzM hyz
      · have hxM : x ∉ M := fun h => hx (hMX h)
        have hU : U.card ≤ X.card + M.card := hcard
        rw [hbiu, Finset.card_union_of_disjoint hdisj.2, hdisj.1, hcard_ins,
            Finset.card_insert_of_notMem hxM]
        omega
    · refine ⟨M, Finset.Subset.trans hMX (Finset.subset_insert x X), hM2, hMdisj, ?_⟩
      have hdiff : (S x \ U).card ≤ 1 := by
        have hle := hle2 x (Finset.mem_insert_self x X)
        by_cases hc2 : (S x).card = 2
        · have hnd : ¬ Disjoint (S x) U := fun hd => hdisj ⟨hc2, hd⟩
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨v, hv1, hv2⟩ := hnd
          have hvinter : v ∈ U ∩ S x := Finset.mem_inter.mpr ⟨hv2, hv1⟩
          have hpos : 1 ≤ (U ∩ S x).card := Finset.card_pos.mpr ⟨v, hvinter⟩
          rw [Finset.card_sdiff]
          omega
        · calc (S x \ U).card ≤ (S x).card := Finset.card_le_card Finset.sdiff_subset
            _ ≤ 1 := by omega
      have hunion : (S x ∪ U).card = U.card + (S x \ U).card := by
        have : S x ∪ U = U ∪ (S x \ U) := by ext v; simp; tauto
        rw [this, Finset.card_union_of_disjoint Finset.sdiff_disjoint.symm]
      have hU : U.card ≤ X.card + M.card := hcard
      rw [hbiu, hunion, hcard_ins]
      omega

lemma pair_of_card_two {m : Nat} {s : Finset (Fin m)} (hc : s.card = 2) :
    ∃ a b : Fin m, a < b ∧ s = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, hlt, rfl⟩
  · exact ⟨y, x, hgt, Finset.pair_comm x y⟩

lemma matching_card_mul_two_le {m : Nat} (M : Finset (Fin m × Fin m))
    (hlt : ∀ e ∈ M, e.1 < e.2)
    (hdisj : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint ({e.1, e.2} : Finset (Fin m)) {f.1, f.2}) :
    (M.biUnion (fun e => ({e.1, e.2} : Finset (Fin m)))).card = 2 * M.card := by
  classical
  rw [Finset.card_biUnion]
  · have hsum : ∑ e ∈ M, ({e.1, e.2} : Finset (Fin m)).card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.card_pair (ne_of_lt (hlt e he))
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro e he f hf hef
    exact hdisj e he f hf hef

lemma length_flatten_ofFn_ofFn {α : Type*} (m : Nat) (f : Fin m → Fin m → α) :
    (List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => f a b))).flatten.length = m * m := by
  rw [List.length_flatten, List.map_ofFn]
  have hfn : (List.length ∘ fun a : Fin m => List.ofFn (fun b : Fin m => f a b)) = fun _ : Fin m => m := by
    funext a; simp
  rw [hfn, List.ofFn_const, List.sum_replicate, smul_eq_mul]

lemma flatten_ofFn_ofFn_getD {α : Type*} (n m : Nat) (f : Fin n → Fin m → α) (d : α) (a : Fin n) (b : Fin m) :
    (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin m => f i j))).flatten.getD (a.val * m + b.val) d = f a b := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n' ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases a using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [getD_append_left _ _ d (by simp)]
      simp [List.getD, b.isLt]
    | succ a' =>
      simp only [Fin.val_succ]
      have hge : m ≤ (a'.val + 1) * m + b.val := by
        have : (a'.val + 1) * m = m + a'.val * m := by ring
        omega
      have hsub : (a'.val + 1) * m + b.val - m = a'.val * m + b.val := by
        have : (a'.val + 1) * m = m + a'.val * m := by ring
        omega
      have hlen0 : (List.ofFn (fun j : Fin m => f 0 j)).length = m := List.length_ofFn
      rw [List.getD, List.getElem?_append_right (hlen0.symm ▸ hge), hlen0, hsub]
      exact ih (fun i j => f i.succ j) a'

lemma flatten_ofFn_append_getD_left {α : Type*} (m : Nat) (f : Fin m → Fin m → α) (tail : List α) (d : α) (a b : Fin m) :
    ((List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => f a b))).flatten ++ tail).getD (a.val * m + b.val) d = f a b := by
  have hlt : a.val * m + b.val < m * m := by
    have ha : a.val + 1 ≤ m := a.isLt
    have hb : b.val < m := b.isLt
    nlinarith
  have hlen := length_flatten_ofFn_ofFn m f
  rw [getD_append_left _ _ d (by omega)]
  exact flatten_ofFn_ofFn_getD m m f d a b

lemma flatten_ofFn_append_getD_right {α : Type*} (m : Nat) (f : Fin m → Fin m → α) (g : Fin m → α) (d : α) (j : Fin m) :
    ((List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => f a b))).flatten ++
      List.ofFn g).getD (m * m + j.val) d = g j := by
  have hlen := length_flatten_ofFn_ofFn m f
  rw [List.getD, List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]
  simp [List.getElem?_ofFn, j.isLt]

lemma graphInput_getD {m : Nat} (G : Finset (Fin m × Fin m)) (a b : Fin m) :
    ((List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => decide ((a, b) ∈ G)))).flatten ++
      [false, true]).getD (a.val * m + b.val) false = decide ((a, b) ∈ G) :=
  flatten_ofFn_append_getD_left m (fun a b => decide ((a, b) ∈ G)) [false, true] false a b

lemma graphInput_length {m : Nat} (G : Finset (Fin m × Fin m)) :
    ((List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => decide ((a, b) ∈ G)))).flatten ++
      [false, true]).length = m * m + 2 := by
  rw [List.length_append, length_flatten_ofFn_ofFn]; rfl

def buildSeqOr (falseW : Nat) : Nat → List (List Nat) → List Gate × List Nat
  | _, [] => ([], [])
  | base, ws :: rest =>
    let r1 := orList base falseW ws
    let r2 := buildSeqOr falseW (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma buildSeqOr_len (falseW base : Nat) (wss : List (List Nat)) :
    (buildSeqOr falseW base wss).1.length ≤ (wss.map List.length).sum ∧
    (buildSeqOr falseW base wss).2.length = wss.length := by
  induction wss generalizing base with
  | nil => simp [buildSeqOr]
  | cons ws rest ih =>
    have h1 := orList_len base falseW ws
    have h2 := ih (base + (orList base falseW ws).1.length)
    simp only [buildSeqOr, List.length_append, List.map_cons, List.sum_cons, List.length_cons]
    exact ⟨by omega, by omega⟩

lemma buildSeqOr_spec (falseW base : Nat) (wss : List (List Nat))
    (hf : falseW < base) (hwss : ∀ ws ∈ wss, ∀ u ∈ ws, u < base) :
    ValidPos base (buildSeqOr falseW base wss).1 ∧
    (∀ o ∈ (buildSeqOr falseW base wss).2, o < base + (buildSeqOr falseW base wss).1.length) ∧
    ∀ (w : List Bool), w.length = base → w.getD falseW false = false →
      ∀ idx < wss.length,
        ((buildSeqOr falseW base wss).1.foldl stepWire w).getD
          ((buildSeqOr falseW base wss).2.getD idx falseW) false =
        (wss.getD idx []).any (fun u => w.getD u false) := by
  induction wss generalizing base with
  | nil =>
    refine ⟨⟨by simp [buildSeqOr], by simp [buildSeqOr]⟩, by simp [buildSeqOr], by simp⟩
  | cons ws rest ih =>
    have h1 := orList_spec base falseW ws hf (hwss ws (by simp))
    let r1 := orList base falseW ws
    have h2 := ih (base + r1.1.length) (Nat.lt_of_lt_of_le hf (Nat.le_add_right _ _))
      (fun ws' hws' u hu => Nat.lt_of_lt_of_le (hwss ws' (by simp [hws']) u hu) (Nat.le_add_right _ _))
    refine ⟨validPos_append h1.1 h2.1, ?_, ?_⟩
    · intro o ho
      simp only [buildSeqOr, List.mem_cons, List.length_append] at ho ⊢
      rcases ho with rfl | ho2
      · exact Nat.lt_of_lt_of_le h1.2.1 (by omega)
      · have := h2.2.1 o ho2; dsimp only [r1] at this; omega
    · intro w hlen hfw idx hidx
      simp only [buildSeqOr, foldl_stepWire_append]
      let w1 := r1.1.foldl stepWire w
      have hlen1 : w1.length = base + r1.1.length := by
        simp [w1, foldl_stepWire_length, hlen]
      have hfw1 : w1.getD falseW false = false := by
        rw [foldl_stepWire_prefix w r1.1 (by omega)]; exact hfw
      cases idx with
      | zero =>
        change ((buildSeqOr falseW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqOr falseW (base + r1.1.length) rest).2).getD 0 falseW) false =
          ((ws :: rest).getD 0 []).any (fun u => w.getD u false)
        simp only [List.getD_cons_zero]
        rw [foldl_stepWire_prefix w1 _ (by rw [hlen1]; exact h1.2.1)]
        exact h1.2.2 w hlen hfw
      | succ idx' =>
        change ((buildSeqOr falseW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqOr falseW (base + r1.1.length) rest).2).getD (idx' + 1) falseW) false =
          ((ws :: rest).getD (idx' + 1) []).any (fun u => w.getD u false)
        simp only [List.getD_cons_succ]
        have hrec := h2.2.2 w1 hlen1 hfw1 idx' (by simp at hidx; omega)
        rw [hrec]
        rw [Bool.eq_iff_iff]
        simp only [List.any_eq_true]
        exact exists_congr fun u => and_congr_right fun hu => by
          have hmem : rest.getD idx' [] ∈ rest := by
            simp only [List.getD, List.getElem?_eq_getElem (by simp at hidx; omega : idx' < rest.length),
              Option.getD_some]
            exact List.getElem_mem _
          have hu' : u < w.length := hlen.symm ▸ hwss _ (List.mem_cons_of_mem ws hmem) u hu
          dsimp only [w1]
          rw [foldl_stepWire_prefix w r1.1 hu']

end PEqualNP.Outside.L_lib_1490_aux

theorem PEqualNP.Outside.L_lib_1490 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let bits := fun {k : Nat} (Y : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]
∀ (m g : Nat),
  let graphInput := fun (G : Finset (Fin m × Fin m)) =>
    (List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m => decide ((a,b) ∈ G)))).flatten ++ [false,true]
  let ranked := fun (G : Finset (Fin m × Fin m)) (t : Nat) =>
    ∃ M : Finset (Fin m × Fin m), M ⊆ G ∧ t ≤ M.card ∧ (∀ e ∈ M, e.1 < e.2) ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint ({e.1,e.2} : Finset (Fin m)) {f.1,f.2}
  let graphFits := fun (bound : Nat) => ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (m+1) → Nat),
    pos (m*m) D ∧ D.size ≤ bound ∧ ∀ t, tap t < m * m + 2 + D.size ∧
      ∀ G, (D.wires (graphInput G)).getD (tap t) false=true ↔ ranked G t.val
  let coverFits := fun {k : Nat} (S : Fin k → Finset (Fin m)) (bound : Nat) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (m+1) → Nat), pos k D ∧ D.size ≤ bound ∧
      ∀ b, tap b < k + 2 + D.size ∧ ∀ I : Finset (Fin k), (D.wires (bits I)).getD (tap b) false=true ↔
        ∃ X : Finset (Fin k), X ⊆ I ∧ X.card ≤ b.val ∧ X.biUnion S=Finset.univ
  let host := (List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m =>
    if a < b then ({a,b} : Finset (Fin m)) else ∅))).flatten ++
      List.ofFn (fun j : Fin m => ({j} : Finset (Fin m)))
  (graphFits g → ∀ (k : Nat) (S : Fin k → Finset (Fin m)),
    (∀ j, (S j).card ≤ 2) → coverFits S (g+3*k+2*m+2)) ∧
  (coverFits (fun j : Fin (m*m+m) => host.getD j.val ∅) g → graphFits g)) := by
  intro valid pos bits m g graphInput ranked graphFits coverFits host
  open PEqualNP.Outside.L_lib_1490_aux in
  have hglen_all : ∀ G : Finset (Fin m × Fin m), (graphInput G).length = m * m + 2 := fun G => by
    dsimp only [graphInput]; rw [List.length_append, length_flatten_ofFn_ofFn]; rfl
  have hgget_all : ∀ (G : Finset (Fin m × Fin m)) (a b : Fin m),
      (graphInput G).getD (a.val * m + b.val) false = decide ((a, b) ∈ G) := fun G a b => by
    dsimp only [graphInput]
    convert flatten_ofFn_append_getD_left m (fun a b : Fin m => decide ((a, b) ∈ G)) [false, true] false a b
  have hgf_all : ∀ G : Finset (Fin m × Fin m), (graphInput G).getD (m * m) false = false := fun G => by
    dsimp only [graphInput]
    rw [List.getD, List.getElem?_append_right (by rw [length_flatten_ofFn_ofFn]),
        length_flatten_ofFn_ofFn, Nat.sub_self]; rfl
  have hgt_all : ∀ G : Finset (Fin m × Fin m), (graphInput G).getD (m * m + 1) false = true := fun G => by
    dsimp only [graphInput]
    rw [List.getD, List.getElem?_append_right (by rw [length_flatten_ofFn_ofFn]; omega),
        length_flatten_ofFn_ofFn, Nat.add_sub_cancel_left]; rfl
  constructor
  · intro ⟨D, tapD, hposD, hszD, htapD⟩ k S hSle2
    have hvD := pos_to_validPos D hposD.1.1 hposD.1.2.1 hposD.2
    let covLists : List (List Nat) :=
      List.ofFn (fun v : Fin m => (List.finRange k).filterMap (fun j => if v ∈ S j then some j.val else none))
    let edgeLists : List (List Nat) :=
      (List.ofFn (fun a : Fin m => List.ofFn (fun b : Fin m =>
        if a < b then
          (List.finRange k).filterMap (fun j => if S j = {a, b} then some j.val else none)
        else []))).flatten
    let rCov := buildSeqOr k (k + 2) covLists
    let b1 := k + 2 + rCov.1.length
    let rAll := andList b1 (k + 1) rCov.2
    let b2 := b1 + rAll.1.length
    let rEdge := buildSeqOr k b2 edgeLists
    let b3 := b2 + rEdge.1.length
    let inpMap : Nat → Nat := fun idx =>
      if idx < m * m then rEdge.2.getD idx k
      else if idx = m * m then k
      else k + 1
    let gRemap := remapGates (m * m + 2) b3 inpMap D.gates
    let b4 := b3 + gRemap.length
    let gOut : List PEqualNP.CircuitLowerBounds.Gate :=
      List.ofFn (fun b : Fin (m + 1) =>
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
          [rAll.2, remapWire (m * m + 2) b3 inpMap (tapD ⟨m - b.val, by omega⟩)]⟩)
    let gsAll := rCov.1 ++ rAll.1 ++ rEdge.1 ++ gRemap ++ gOut
    let D' : PEqualNP.CircuitLowerBounds.Circuit := ⟨gsAll, k⟩
    let tap' : Fin (m + 1) → Nat := fun b => b4 + b.val
    have hcov_in : ∀ ws ∈ covLists, ∀ u ∈ ws, u < k + 2 := by
      intro ws hws u hu
      simp only [covLists, List.mem_ofFn] at hws
      obtain ⟨v, rfl⟩ := hws
      simp only [List.mem_filterMap] at hu
      obtain ⟨j, _, hj⟩ := hu
      split_ifs at hj
      injection hj with hju; subst hju; omega
    have hcov_sp := buildSeqOr_spec k (k + 2) covLists (by omega) hcov_in
    have hall_sp := andList_spec b1 (k + 1) rCov.2 (by omega) hcov_sp.2.1
    have hedge_in : ∀ ws ∈ edgeLists, ∀ u ∈ ws, u < b2 := by
      intro ws hws u hu
      simp only [edgeLists, List.mem_flatten, List.mem_ofFn] at hws
      obtain ⟨l, ⟨a, rfl⟩, hl⟩ := hws
      simp only [List.mem_ofFn] at hl
      obtain ⟨b, rfl⟩ := hl
      split_ifs at hu
      · simp only [List.mem_filterMap] at hu
        obtain ⟨j, _, hj⟩ := hu
        split_ifs at hj
        injection hj with hju; subst hju; omega
      · simp at hu
    have hedge_sp := buildSeqOr_spec k b2 edgeLists (by omega) hedge_in
    have hmap_lt : ∀ i < m * m + 2, inpMap i < b3 := by
      intro i hi
      dsimp only [inpMap]
      split_ifs with h1 h2
      · by_cases hi2 : i < rEdge.2.length
        · have hmem : rEdge.2.getD i k ∈ rEdge.2 := by
            simp only [List.getD, List.getElem?_eq_getElem hi2, Option.getD_some]
            exact List.getElem_mem _
          exact hedge_sp.2.1 _ hmem
        · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hi2), Option.getD_none]
          omega
      · omega
      · omega
    have hrem_v := remapGates_valid hvD hmap_lt
    have hout_v : ValidPos b4 gOut := by
      constructor
      · intro g hg
        simp only [gOut, List.mem_ofFn] at hg
        obtain ⟨b, rfl⟩ := hg
        exact ⟨Or.inl rfl, by simp⟩
      · intro j hj i hi
        simp only [gOut, List.length_ofFn] at hj
        have hget : gOut.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ =
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
              [rAll.2, remapWire (m * m + 2) b3 inpMap (tapD ⟨m - j, by omega⟩)]⟩ := by
          simp only [gOut, List.getD, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
        rw [hget] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have := hall_sp.2.1; dsimp only [b4, b3, b2, b1, rAll, rCov, rEdge, gRemap] at *; omega
        · have ht := (htapD ⟨m - j, by omega⟩).1
          unfold remapWire
          split_ifs with hlt
          · have := hmap_lt _ hlt; dsimp only [b4, b3, b2, b1, rAll, rCov, rEdge, gRemap] at *; omega
          · have hgl : gRemap.length = D.size := by simp [gRemap, remapGates, PEqualNP.CircuitLowerBounds.Circuit.size]
            dsimp only [b4, b3, b2, b1] at *; omega
    have hvalid_all : ValidPos (k + 2) gsAll := by
      have h12 := validPos_append hcov_sp.1 hall_sp.1
      have h123 : ValidPos (k + 2) (rCov.1 ++ rAll.1 ++ rEdge.1) := by
        apply validPos_append h12
        have heq : k + 2 + (rCov.1 ++ rAll.1).length = b2 := by
          simp only [b2, b1, List.length_append, Nat.add_assoc]
        exact heq ▸ hedge_sp.1
      have h1234 : ValidPos (k + 2) (rCov.1 ++ rAll.1 ++ rEdge.1 ++ gRemap) := by
        apply validPos_append h123
        have heq : k + 2 + (rCov.1 ++ rAll.1 ++ rEdge.1).length = b3 := by
          simp only [b3, b2, b1, List.length_append, Nat.add_assoc]
        exact heq ▸ hrem_v
      apply validPos_append h1234
      have heq : k + 2 + (rCov.1 ++ rAll.1 ++ rEdge.1 ++ gRemap).length = b4 := by
        simp only [b4, b3, b2, b1, List.length_append, Nat.add_assoc]
      exact heq ▸ hout_v
    have hcov_sum : (covLists.map List.length).sum ≤ 2 * k := by
      have h1 : (covLists.map List.length).sum = ∑ v : Fin m, (Finset.univ.filter (fun j : Fin k => v ∈ S j)).card := by
        simp only [covLists, List.map_ofFn, List.sum_ofFn]
        apply Finset.sum_congr rfl
        intro v _
        dsimp only [Function.comp_apply]
        have hfl : ((List.finRange k).filterMap (fun j => if v ∈ S j then some j.val else none)).length =
            ((List.finRange k).filter (fun j => decide (v ∈ S j))).length := by
          clear hcov_in hcov_sp hall_sp hedge_in hedge_sp hmap_lt hrem_v hout_v hvalid_all
          induction (List.finRange k) with
          | nil => rfl
          | cons j rest ih =>
            by_cases hv : v ∈ S j <;> simp [hv, ih]
        rw [hfl]
        have : (Finset.univ.filter (fun j : Fin k => v ∈ S j)).card =
            ((List.finRange k).filter (fun j => decide (v ∈ S j))).length := by
          have hnodup : ((List.finRange k).filter (fun j => decide (v ∈ S j))).Nodup :=
            (List.nodup_finRange k).filter _
          rw [← List.toFinset_card_of_nodup hnodup]
          congr 1; ext j; simp
        exact this.symm
      rw [h1]
      have hswap : ∑ v : Fin m, (Finset.univ.filter (fun j : Fin k => v ∈ S j)).card =
          ∑ j : Fin k, (S j).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.card_filter]
        congr 1; ext v; simp
      rw [hswap]
      calc ∑ j : Fin k, (S j).card ≤ ∑ _j : Fin k, 2 := Finset.sum_le_sum (fun j _ => hSle2 j)
        _ = 2 * k := by simp [mul_comm]
    have hedge_sum : (edgeLists.map List.length).sum ≤ k := by
      have hlen_flat : (edgeLists.map List.length).sum =
          ∑ a : Fin m, ∑ b : Fin m,
            if a < b then (Finset.univ.filter (fun j : Fin k => S j = {a, b})).card else 0 := by
        simp only [edgeLists, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]
        apply Finset.sum_congr rfl
        intro a _
        simp only [Function.comp_apply, List.map_ofFn, List.sum_ofFn]
        apply Finset.sum_congr rfl
        intro b _
        split_ifs with hab
        · have hfl : ((List.finRange k).filterMap (fun j => if S j = {a, b} then some j.val else none)).length =
              ((List.finRange k).filter (fun j => decide (S j = {a, b}))).length := by
            clear hcov_in hcov_sp hall_sp hedge_in hedge_sp hmap_lt hrem_v hout_v hvalid_all hcov_sum
            induction (List.finRange k) with
            | nil => rfl
            | cons j rest ih =>
              by_cases hj : S j = {a, b} <;> simp [hj, ih]
          rw [hfl]
          have hnodup : ((List.finRange k).filter (fun j => decide (S j = {a, b}))).Nodup :=
            (List.nodup_finRange k).filter _
          rw [← List.toFinset_card_of_nodup hnodup]
          congr 1; ext j; simp
        · rfl
      rw [hlen_flat]
      have hswap : ∑ a : Fin m, ∑ b : Fin m,
            (if a < b then (Finset.univ.filter (fun j : Fin k => S j = {a, b})).card else 0) =
          ∑ j : Fin k, ∑ a : Fin m, ∑ b : Fin m, if a < b ∧ S j = {a, b} then 1 else 0 := by
        trans ∑ a : Fin m, ∑ b : Fin m, ∑ j : Fin k, if a < b ∧ S j = {a, b} then 1 else 0
        · apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          split_ifs with hab
          · rw [Finset.card_filter]
            apply Finset.sum_congr rfl; intro j _
            simp [hab]
          · simp [hab]
        · calc ∑ a : Fin m, ∑ b : Fin m, ∑ j : Fin k, (if a < b ∧ S j = {a, b} then 1 else 0)
              = ∑ a : Fin m, ∑ j : Fin k, ∑ b : Fin m, (if a < b ∧ S j = {a, b} then 1 else 0) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = ∑ j : Fin k, ∑ a : Fin m, ∑ b : Fin m, (if a < b ∧ S j = {a, b} then 1 else 0) :=
                Finset.sum_comm
      rw [hswap]
      have hle1 : ∀ j : Fin k, (∑ a : Fin m, ∑ b : Fin m, if a < b ∧ S j = {a, b} then 1 else 0) ≤ 1 := by
        intro j
        by_cases hc : (S j).card = 2
        · obtain ⟨a0, b0, hab0, heq0⟩ := pair_of_card_two hc
          have huniq : ∀ a b : Fin m, a < b ∧ S j = {a, b} → a = a0 ∧ b = b0 := by
            intro a b ⟨hab, heq⟩
            rw [heq0] at heq
            have ha : a ∈ ({a0, b0} : Finset (Fin m)) := by rw [heq]; simp
            have hb : b ∈ ({a0, b0} : Finset (Fin m)) := by rw [heq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (lt_irrefl _)
            · exact ⟨rfl, rfl⟩
            · exact absurd (lt_trans hab hab0) (lt_irrefl _)
            · exact absurd hab (lt_irrefl _)
          calc ∑ a : Fin m, ∑ b : Fin m, (if a < b ∧ S j = {a, b} then 1 else 0)
              ≤ ∑ a : Fin m, ∑ b : Fin m, (if a = a0 ∧ b = b0 then 1 else 0) := by
                apply Finset.sum_le_sum; intro a _
                apply Finset.sum_le_sum; intro b _
                split_ifs with h1 h2
                · exact le_rfl
                · exact absurd (huniq a b h1) h2
                · exact Nat.zero_le _
                · exact le_rfl
            _ = ∑ a : Fin m, if a = a0 then 1 else 0 := by
                apply Finset.sum_congr rfl; intro a _
                split_ifs with ha <;> simp [ha]
            _ = 1 := by simp
        · have hzero : ∀ a b : Fin m, ¬ (a < b ∧ S j = {a, b}) := by
            intro a b ⟨hab, heq⟩
            apply hc; rw [heq, Finset.card_pair (ne_of_lt hab)]
          simp [hzero]
      calc ∑ j : Fin k, (∑ a : Fin m, ∑ b : Fin m, if a < b ∧ S j = {a, b} then 1 else 0)
          ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum (fun j _ => hle1 j)
        _ = k := by simp
    have hszD' : D'.size ≤ g + 3 * k + 2 * m + 2 := by
      have h1 := (buildSeqOr_len k (k + 2) covLists).1
      have h2 := andList_len b1 (k + 1) rCov.2
      have h2' : rCov.2.length = m := by
        rw [(buildSeqOr_len k (k + 2) covLists).2]; simp [covLists]
      have h3 := (buildSeqOr_len k b2 edgeLists).1
      have h4 : gRemap.length = D.size := by simp [gRemap, remapGates, PEqualNP.CircuitLowerBounds.Circuit.size]
      have h5 : gOut.length = m + 1 := by simp [gOut]
      simp only [D', gsAll, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append]
      dsimp only [rCov, rAll, rEdge] at *
      omega
    have hposD' := validPos_to_pos D' hvalid_all (by simp [D', gsAll]; omega)
    refine ⟨D', tap', ⟨⟨hposD'.1, hposD'.2.1, hposD'.2.2.1⟩, hposD'.2.2.2⟩, hszD', ?_⟩
    intro b
    refine ⟨?_, ?_⟩
    · simp only [tap', D', gsAll, b4, b3, b2, b1, gOut, PEqualNP.CircuitLowerBounds.Circuit.size,
        List.length_append, List.length_ofFn]
      omega
    · intro I
      let xI := bits I
      have hxI_len : xI.length = k + 2 := by simp [xI, bits]
      have hxI_f : xI.getD k false = false := by
        dsimp only [xI, bits]
        rw [List.getD, List.getElem?_append_right (by simp), List.length_ofFn, Nat.sub_self]; rfl
      have hxI_t : xI.getD (k + 1) false = true := by
        dsimp only [xI, bits]
        rw [List.getD, List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]; rfl
      have hxI_bit : ∀ j : Fin k, xI.getD j.val false = decide (j ∈ I) := by
        intro j
        dsimp only [xI, bits]
        rw [List.getD, List.getElem?_append_left (by simp)]
        simp [j.isLt]
      let w1 := rCov.1.foldl stepWire xI
      let w2 := rAll.1.foldl stepWire w1
      let w3 := rEdge.1.foldl stepWire w2
      let w4 := gRemap.foldl stepWire w3
      let w5 := gOut.foldl stepWire w4
      have hw1_len : w1.length = b1 := by simp [w1, foldl_stepWire_length, hxI_len, b1]
      have hw2_len : w2.length = b2 := by simp [w2, foldl_stepWire_length, hw1_len, b2]
      have hw3_len : w3.length = b3 := by simp [w3, foldl_stepWire_length, hw2_len, b3]
      have hw4_len : w4.length = b4 := by simp [w4, foldl_stepWire_length, hw3_len, b4]
      have hw_eq : D'.wires xI = w5 := by
        simp only [D', gsAll, PEqualNP.CircuitLowerBounds.Circuit.wires]
        change (rCov.1 ++ rAll.1 ++ rEdge.1 ++ gRemap ++ gOut).foldl stepWire xI = w5
        simp only [foldl_stepWire_append, w1, w2, w3, w4, w5]
      rw [hw_eq]
      have hw1_cov : ∀ v : Fin m, w1.getD (rCov.2.getD v.val k) false = decide (∃ j ∈ I, v ∈ S j) := by
        intro v
        have hsp := hcov_sp.2.2 xI hxI_len hxI_f v.val (by simp [covLists])
        rw [hsp]
        have hget : covLists.getD v.val [] =
            (List.finRange k).filterMap (fun j => if v ∈ S j then some j.val else none) := by
          simp only [covLists, List.getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte, Option.getD_some]
        rw [hget]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_filterMap, decide_eq_true_eq]
        constructor
        · rintro ⟨u, ⟨j, _, hj⟩, hu⟩
          split_ifs at hj with hv
          injection hj with hju; subst hju
          rw [hxI_bit j, decide_eq_true_eq] at hu
          exact ⟨j, hu, hv⟩
        · rintro ⟨j, hjI, hv⟩
          exact ⟨j.val, ⟨j, List.mem_finRange j, by simp [hv]⟩, by rw [hxI_bit j, decide_eq_true_eq]; exact hjI⟩
      have hw2_all : w2.getD rAll.2 false = decide (∀ v : Fin m, ∃ j ∈ I, v ∈ S j) := by
        have ht1 : w1.getD (k + 1) false = true := by
          rw [foldl_stepWire_prefix xI rCov.1 (by omega)]; exact hxI_t
        rw [hall_sp.2.2 w1 hw1_len ht1]
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, decide_eq_true_eq]
        have hlen_cov : rCov.2.length = m := by
          rw [(buildSeqOr_len k (k + 2) covLists).2]; simp [covLists]
        constructor
        · intro hall v
          have hmem : rCov.2.getD v.val k ∈ rCov.2 := by
            simp only [List.getD, List.getElem?_eq_getElem (by omega : v.val < rCov.2.length), Option.getD_some]
            exact List.getElem_mem _
          have h := hall _ hmem
          rw [hw1_cov v, decide_eq_true_eq] at h
          exact h
        · intro hall u hu
          obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hu
          have hv : idx < m := by omega
          have hget : rCov.2[idx] = rCov.2.getD idx k := by
            simp [List.getD, hidx]
          rw [hget, hw1_cov ⟨idx, hv⟩, decide_eq_true_eq]
          exact hall ⟨idx, hv⟩
      let GI : Finset (Fin m × Fin m) :=
        Finset.univ.filter (fun p => p.1 < p.2 ∧ ∃ j ∈ I, S j = {p.1, p.2})
      have hw3_edge : ∀ (a b : Fin m), w3.getD (rEdge.2.getD (a.val * m + b.val) k) false = decide ((a, b) ∈ GI) := by
        intro a b
        have hf2 : w2.getD k false = false := by
          rw [foldl_stepWire_prefix w1 rAll.1 (by omega), foldl_stepWire_prefix xI rCov.1 (by omega)]
          exact hxI_f
        have hlt_ab : a.val * m + b.val < m * m := by
          have ha : a.val + 1 ≤ m := a.isLt
          have hb : b.val < m := b.isLt
          nlinarith
        have hlen_el : edgeLists.length = m * m := length_flatten_ofFn_ofFn m _
        have hsp := hedge_sp.2.2 w2 hw2_len hf2 (a.val * m + b.val) (by omega)
        rw [hsp]
        have hget : edgeLists.getD (a.val * m + b.val) [] =
            if a < b then (List.finRange k).filterMap (fun j => if S j = {a, b} then some j.val else none) else [] :=
          flatten_ofFn_ofFn_getD m m _ [] a b
        rw [hget]
        apply Bool.eq_iff_iff.mpr
        simp only [GI, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        split_ifs with hab
        · simp only [List.any_eq_true, List.mem_filterMap, hab, true_and]
          constructor
          · rintro ⟨u, ⟨j, _, hj⟩, hu⟩
            split_ifs at hj with heq
            injection hj with hju; subst hju
            rw [foldl_stepWire_prefix w1 rAll.1 (by omega),
                foldl_stepWire_prefix xI rCov.1 (by omega),
                hxI_bit j, decide_eq_true_eq] at hu
            exact ⟨j, hu, heq⟩
          · rintro ⟨j, hjI, heq⟩
            refine ⟨j.val, ⟨j, List.mem_finRange j, by simp [heq]⟩, ?_⟩
            rw [foldl_stepWire_prefix w1 rAll.1 (by omega),
                foldl_stepWire_prefix xI rCov.1 (by omega),
                hxI_bit j, decide_eq_true_eq]
            exact hjI
        · simp [hab]
      have hagree_GI : ∀ i < m * m + 2, w3.getD (inpMap i) false = (graphInput GI).getD i false := by
        intro i hi
        dsimp only [inpMap]
        split_ifs with h1 h2
        · have hm0 : 0 < m := by
            by_contra h0; have : m = 0 := by omega
            subst this; omega
          let a : Fin m := ⟨i / m, Nat.div_lt_of_lt_mul h1⟩
          let b' : Fin m := ⟨i % m, Nat.mod_lt i hm0⟩
          have hi_eq : a.val * m + b'.val = i := by
            dsimp only [a, b']; rw [mul_comm]; exact Nat.div_add_mod i m
          rw [← hi_eq, hw3_edge a b', hgget_all GI a b']
        · subst h2
          rw [foldl_stepWire_prefix w2 rEdge.1 (by omega),
              foldl_stepWire_prefix w1 rAll.1 (by omega),
              foldl_stepWire_prefix xI rCov.1 (by omega), hxI_f, hgf_all GI]
        · have hi_eq : i = m * m + 1 := by omega
          subst hi_eq
          rw [foldl_stepWire_prefix w2 rEdge.1 (by omega),
              foldl_stepWire_prefix w1 rAll.1 (by omega),
              foldl_stepWire_prefix xI rCov.1 (by omega), hxI_t, hgt_all GI]
      have hw4_rem := remapGates_eval inpMap D.gates (graphInput GI) w3
        (hglen_all GI) hw3_len hmap_lt hagree_GI
      have hw5_b : w5.getD (tap' b) false =
          (w4.getD rAll.2 false && w4.getD (remapWire (m * m + 2) b3 inpMap (tapD ⟨m - b.val, by omega⟩)) false) := by
        have hstep_out : ∀ (n : Nat) (f : Fin n → PEqualNP.CircuitLowerBounds.Gate) (w0 : List Bool) (j : Fin n),
            (∀ i : Fin n, ∀ u ∈ (f i).inputs, u < w0.length) →
            ((List.ofFn f).foldl stepWire w0).getD (w0.length + j.val) false =
            (f j).op.eval ((f j).inputs.map fun u => w0.getD u false) := by
          intro n
          induction n with
          | zero => intro _ _ j; exact Fin.elim0 j
          | succ n' ih =>
            intro f w0 j hlt
            rw [List.ofFn_succ, List.foldl_cons]
            cases j using Fin.cases with
            | zero =>
              simp only [Fin.val_zero, Nat.add_zero]
              rw [foldl_stepWire_prefix (stepWire w0 (f 0)) _ (by simp [stepWire])]
              simp only [stepWire, getD_singleton_last]
            | succ j' =>
              have hlt' : ∀ i : Fin n', ∀ u ∈ (f i.succ).inputs, u < (stepWire w0 (f 0)).length := by
                intro i u hu; simp [stepWire]; exact Nat.le_of_lt (hlt i.succ u hu)
              have hrec := ih (fun i => f i.succ) (stepWire w0 (f 0)) j' hlt'
              have hlen_s : (stepWire w0 (f 0)).length + j'.val = w0.length + j'.succ.val := by
                simp [stepWire]; omega
              rw [← hlen_s, hrec]
              congr 1
              apply List.map_congr_left
              intro u hu
              exact getD_append_left w0 _ false (hlt j'.succ u hu)
        have hlt_out : ∀ i : Fin (m + 1), ∀ u ∈ ([rAll.2, remapWire (m * m + 2) b3 inpMap (tapD ⟨m - i.val, by omega⟩)] : List Nat), u < w4.length := by
          intro i u hu
          rw [hw4_len]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · have := hall_sp.2.1; dsimp only [b4, b3, b2, b1, rAll, rCov, rEdge, gRemap] at *; omega
          · have ht := (htapD ⟨m - i.val, by omega⟩).1
            unfold remapWire
            split_ifs with hlt
            · have := hmap_lt _ hlt; dsimp only [b4, b3, b2, b1, rAll, rCov, rEdge, gRemap] at *; omega
            · have hgl : gRemap.length = D.size := by simp [gRemap, remapGates, PEqualNP.CircuitLowerBounds.Circuit.size]
              dsimp only [b4, b3, b2, b1] at *; omega
        have h := hstep_out (m + 1) (fun b : Fin (m + 1) =>
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
            [rAll.2, remapWire (m * m + 2) b3 inpMap (tapD ⟨m - b.val, by omega⟩)]⟩) w4 b hlt_out
        change (gOut.foldl stepWire w4).getD (b4 + b.val) false = _
        rw [← hw4_len]
        rw [h]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      rw [hw5_b]
      have hw4_all : w4.getD rAll.2 false = decide (∀ v : Fin m, ∃ j ∈ I, v ∈ S j) := by
        rw [foldl_stepWire_prefix w3 gRemap (by rw [hw3_len]; have := hall_sp.2.1; dsimp only [b3, b2, b1, rAll] at *; omega),
            foldl_stepWire_prefix w2 rEdge.1 (by rw [hw2_len]; exact hall_sp.2.1),
            hw2_all]
      have hw4_tap : w4.getD (remapWire (m * m + 2) b3 inpMap (tapD ⟨m - b.val, by omega⟩)) false =
          (D.wires (graphInput GI)).getD (tapD ⟨m - b.val, by omega⟩) false :=
        hw4_rem (tapD ⟨m - b.val, by omega⟩) (htapD ⟨m - b.val, by omega⟩).1
      rw [hw4_all, hw4_tap, Bool.and_eq_true, decide_eq_true_eq, (htapD ⟨m - b.val, by omega⟩).2 GI]
      constructor
      · rintro ⟨hallCov, ⟨M, hMG, hMcard, hMlt, hMdisj⟩⟩
        have hMsub : m - b.val ≤ M.card := hMcard
        obtain ⟨M', hM'M, hM'card⟩ := Finset.exists_subset_card_eq hMsub
        have hM'lt : ∀ e ∈ M', e.1 < e.2 := fun e he => hMlt e (hM'M he)
        have hM'disj : ∀ e ∈ M', ∀ f ∈ M', e ≠ f → Disjoint ({e.1, e.2} : Finset (Fin m)) {f.1, f.2} :=
          fun e he f hf hef => by convert hMdisj e (hM'M he) f (hM'M hf) hef
        have hpick_e : ∀ e ∈ M', ∃ j ∈ I, S j = {e.1, e.2} := by
          intro e he
          have heG := hMG (hM'M he)
          simp only [GI, Finset.mem_filter, Finset.mem_univ, true_and] at heG
          exact heG.2
        choose fE hfE_I hfE_S using hpick_e
        choose fV hfV_I hfV_in using hallCov
        let covV := M'.biUnion (fun e => ({e.1, e.2} : Finset (Fin m)))
        have hcovV_card : covV.card = 2 * M'.card := by
          convert matching_card_mul_two_le M' hM'lt (fun e he f hf hef => by convert hM'disj e he f hf hef)
        let XE : Finset (Fin k) := M'.attach.image (fun e => fE e.1 e.2)
        let XV : Finset (Fin k) := (Finset.univ \ covV).image fV
        refine ⟨XE ∪ XV, ?_, ?_, ?_⟩
        · refine Finset.union_subset ?_ ?_
          · intro j hj
            obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hj
            exact hfE_I e.1 e.2
          · intro j hj
            obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
            exact hfV_I v
        · have hXE_le : XE.card ≤ M'.card := by
            calc XE.card ≤ M'.attach.card := Finset.card_image_le
              _ = M'.card := Finset.card_attach
          have hXV_le : XV.card ≤ (Finset.univ \ covV).card := Finset.card_image_le
          have hrem : (Finset.univ \ covV).card = m - 2 * M'.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
                Finset.card_univ, Fintype.card_fin, hcovV_card]
          have h2le : 2 * M'.card ≤ m := by
            rw [← hcovV_card]
            calc covV.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = m := by simp
          calc (XE ∪ XV).card ≤ XE.card + XV.card := Finset.card_union_le _ _
            _ ≤ M'.card + (m - 2 * M'.card) := Nat.add_le_add hXE_le (hrem ▸ hXV_le)
            _ ≤ b.val := by omega
        · ext v
          simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hv : v ∈ covV
          · simp only [covV, Finset.mem_biUnion] at hv
            obtain ⟨e, heM', hve⟩ := hv
            refine ⟨fE e heM', Or.inl (Finset.mem_image.mpr ⟨⟨e, heM'⟩, Finset.mem_attach _ _, rfl⟩), ?_⟩
            rw [hfE_S e heM']; exact hve
          · refine ⟨fV v, Or.inr (Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩), hfV_in v⟩
      · rintro ⟨X, hXI, hXcard, hXcov⟩
        have hXcov' : X.biUnion S = Finset.univ := by convert hXcov
        constructor
        · intro v
          have hv : v ∈ X.biUnion S := by rw [hXcov']; exact Finset.mem_univ v
          obtain ⟨j, hjX, hvj⟩ := Finset.mem_biUnion.mp hv
          exact ⟨j, hXI hjX, hvj⟩
        · obtain ⟨M0, hM0X, hM02, hM0disj, hM0card⟩ :=
            matching_of_cover_le2 S X (fun j _ => hSle2 j)
          have hM0_ge : m - b.val ≤ M0.card := by
            rw [hXcov', Finset.card_univ, Fintype.card_fin] at hM0card
            omega
          have hpair : ∀ j ∈ M0, ∃ p : Fin m × Fin m, p.1 < p.2 ∧ S j = {p.1, p.2} := by
            intro j hj
            obtain ⟨a, b', hab, heq⟩ := pair_of_card_two (hM02 j hj)
            exact ⟨(a, b'), hab, heq⟩
          choose gP hgPlt hgPS using hpair
          let M : Finset (Fin m × Fin m) := M0.attach.image (fun j => gP j.1 j.2)
          have hinj : Set.InjOn (fun j : {x // x ∈ M0} => gP j.1 j.2) M0.attach := by
            intro j1 _ j2 _ heq
            dsimp only at heq
            by_contra hne
            have hne' : j1.1 ≠ j2.1 := fun h => hne (Subtype.ext h)
            have hd := hM0disj j1.1 j1.2 j2.1 j2.2 hne'
            rw [hgPS j1.1 j1.2, hgPS j2.1 j2.2, heq] at hd
            exact Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
          have hMcard : M.card = M0.card := by
            rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
          refine ⟨M, ?_, by rw [hMcard]; exact hM0_ge, ?_, ?_⟩
          · intro p hp
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
            simp only [GI, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hgPlt j.1 j.2, j.1, hXI (hM0X j.2), hgPS j.1 j.2⟩
          · intro p hp
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
            exact hgPlt j.1 j.2
          · intro p hp q hq hpq
            obtain ⟨j1, _, rfl⟩ := Finset.mem_image.mp hp
            obtain ⟨j2, _, rfl⟩ := Finset.mem_image.mp hq
            have hne : j1.1 ≠ j2.1 := fun h => hpq (by congr 1)
            have hd := hM0disj j1.1 j1.2 j2.1 j2.2 hne
            rw [hgPS j1.1 j1.2, hgPS j2.1 j2.2] at hd
            convert hd
  · intro ⟨D, tapC, hposC, hszC, htapC⟩
    have hvC := pos_to_validPos D hposC.1.1 hposC.1.2.1 hposC.2
    let n_old := m * m + m + 2
    let base := m * m + 2
    let inpMap : Nat → Nat := fun idx =>
      if idx < m * m then idx
      else if idx < m * m + m then m * m + 1
      else if idx = m * m + m then m * m
      else m * m + 1
    let gRemap := remapGates n_old base inpMap D.gates
    let D' : PEqualNP.CircuitLowerBounds.Circuit := ⟨gRemap, m * m⟩
    let tap' : Fin (m + 1) → Nat := fun t => remapWire n_old base inpMap (tapC ⟨m - t.val, by omega⟩)
    have hmap_lt : ∀ i < n_old, inpMap i < base := by
      intro i hi; dsimp only [inpMap, base, n_old] at *; split_ifs <;> omega
    have hv' := remapGates_valid hvC hmap_lt
    have hsz' : D'.size ≤ g := by
      simpa [D', gRemap, remapGates, PEqualNP.CircuitLowerBounds.Circuit.size] using hszC
    have hpos' := validPos_to_pos D' hv' (by simp [D', gRemap]; omega)
    refine ⟨D', tap', ⟨⟨hpos'.1, hpos'.2.1, hpos'.2.2.1⟩, hpos'.2.2.2⟩, hsz', ?_⟩
    intro t
    refine ⟨?_, ?_⟩
    · have ht := (htapC ⟨m - t.val, by omega⟩).1
      simp only [tap', D', gRemap, remapGates, List.length_map, PEqualNP.CircuitLowerBounds.Circuit.size,
        remapWire, n_old, base] at *
      split_ifs with hlt
      · have := hmap_lt _ hlt; omega
      · omega
    · intro G
      let IG : Finset (Fin (m * m + m)) :=
        Finset.univ.filter (fun j =>
          if hlt : j.val < m * m then
            let hm0 : 0 < m := by
              by_contra h0; have : m = 0 := by omega
              subst this; omega
            (⟨j.val / m, Nat.div_lt_of_lt_mul hlt⟩, ⟨j.val % m, Nat.mod_lt j.val hm0⟩) ∈ G
          else True)
      have hagree : ∀ i < n_old, (graphInput G).getD (inpMap i) false = (bits IG).getD i false := by
        intro i hi
        dsimp only [inpMap]
        split_ifs with h1 h2 h3
        · have hm0 : 0 < m := by
            by_contra h0; have : m = 0 := by omega
            subst this; omega
          let a : Fin m := ⟨i / m, Nat.div_lt_of_lt_mul h1⟩
          let b' : Fin m := ⟨i % m, Nat.mod_lt i hm0⟩
          have hi_eq : a.val * m + b'.val = i := by
            dsimp only [a, b']; rw [mul_comm]; exact Nat.div_add_mod i m
          rw [← hi_eq, hgget_all G a b']
          have hlt2 : i < m * m + m := by omega
          dsimp only [bits]
          rw [List.getD, List.getElem?_append_left (by simp [hi_eq, hlt2])]
          simp only [hi_eq, List.getElem?_ofFn, hlt2, ↓reduceDIte, Option.getD_some,
            IG, Finset.mem_filter, Finset.mem_univ, true_and, h1]
          rfl
        · rw [hgt_all G]
          dsimp only [bits]
          rw [List.getD, List.getElem?_append_left (by simp [h2])]
          simp [IG, h2, h1]
        · subst h3
          rw [hgf_all G]
          dsimp only [bits]
          rw [List.getD, List.getElem?_append_right (by simp), List.length_ofFn, Nat.sub_self]; rfl
        · have hi_eq : i = m * m + m + 1 := by dsimp only [n_old] at hi; omega
          subst hi_eq
          rw [hgt_all G]
          dsimp only [bits]
          rw [List.getD, List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]; rfl
      have hbits_len : (bits IG).length = n_old := by simp [bits, n_old]
      have hrem := remapGates_eval inpMap D.gates (bits IG) (graphInput G)
        hbits_len (hglen_all G) hmap_lt hagree
      have hev : (D'.wires (graphInput G)).getD (tap' t) false =
          (D.wires (bits IG)).getD (tapC ⟨m - t.val, by omega⟩) false :=
        hrem (tapC ⟨m - t.val, by omega⟩) (htapC ⟨m - t.val, by omega⟩).1
      rw [hev, (htapC ⟨m - t.val, by omega⟩).2 IG]
      let Shost : Fin (m * m + m) → Finset (Fin m) := fun j => host.getD j.val ∅
      have hShost_edge : ∀ a b : Fin m,
          host.getD (a.val * m + b.val) ∅ = if a < b then ({a, b} : Finset (Fin m)) else ∅ := fun a b => by
        dsimp only [host]
        convert flatten_ofFn_append_getD_left m
          (fun a b : Fin m => if a < b then ({a, b} : Finset (Fin m)) else ∅)
          (List.ofFn (fun j : Fin m => ({j} : Finset (Fin m)))) ∅ a b
      have hShost_sing : ∀ j : Fin m, host.getD (m * m + j.val) ∅ = {j} := fun j => by
        dsimp only [host]; exact flatten_ofFn_append_getD_right m _ _ ∅ j
      have hShost_le2 : ∀ j : Fin (m * m + m), (Shost j).card ≤ 2 := by
        intro j
        by_cases hj : j.val < m * m
        · have hm0 : 0 < m := by
            by_contra h0; have : m = 0 := by omega
            subst this; omega
          let a : Fin m := ⟨j.val / m, Nat.div_lt_of_lt_mul hj⟩
          let b' : Fin m := ⟨j.val % m, Nat.mod_lt j.val hm0⟩
          have hj_eq : a.val * m + b'.val = j.val := by
            dsimp only [a, b']; rw [mul_comm]; exact Nat.div_add_mod j.val m
          dsimp only [Shost]; rw [← hj_eq, hShost_edge a b']
          split_ifs
          · exact Finset.card_le_two
          · simp
        · let v : Fin m := ⟨j.val - m * m, by omega⟩
          have hj_eq : m * m + v.val = j.val := by dsimp only [v]; omega
          dsimp only [Shost]; rw [← hj_eq, hShost_sing v]; simp
      constructor
      · rintro ⟨X, hXI, hXcard, hXcov⟩
        have hXcov' : X.biUnion Shost = Finset.univ := by convert hXcov
        obtain ⟨M0, hM0X, hM02, hM0disj, hM0card⟩ :=
          matching_of_cover_le2 Shost X (fun j _ => hShost_le2 j)
        have hM0_ge : t.val ≤ M0.card := by
          rw [hXcov', Finset.card_univ, Fintype.card_fin] at hM0card
          dsimp only at hXcard
          omega
        have hM0_lt : ∀ j ∈ M0, j.val < m * m := by
          intro j hj
          by_contra hge
          let v : Fin m := ⟨j.val - m * m, by omega⟩
          have hj_eq : m * m + v.val = j.val := by dsimp only [v]; omega
          have hc := hM02 j hj
          dsimp only [Shost] at hc; rw [← hj_eq, hShost_sing v] at hc
          simp at hc
        have hm0_of : ∀ j ∈ M0, 0 < m := by
          intro j hj
          have hlt := hM0_lt j hj
          by_contra h0; have : m = 0 := by omega
          subst this; omega
        let edgeOf : {j : Fin (m * m + m) // j ∈ M0} → Fin m × Fin m := fun j =>
          (⟨j.1.val / m, Nat.div_lt_of_lt_mul (hM0_lt j.1 j.2)⟩,
           ⟨j.1.val % m, Nat.mod_lt j.1.val (hm0_of j.1 j.2)⟩)
        have hedge_spec : ∀ j : {j : Fin (m * m + m) // j ∈ M0},
            (edgeOf j).1 < (edgeOf j).2 ∧ Shost j.1 = {(edgeOf j).1, (edgeOf j).2} ∧ edgeOf j ∈ G := by
          intro j
          have hlt := hM0_lt j.1 j.2
          have hm0 := hm0_of j.1 j.2
          have hj_eq : (edgeOf j).1.val * m + (edgeOf j).2.val = j.1.val := by
            dsimp only [edgeOf]; rw [mul_comm]; exact Nat.div_add_mod j.1.val m
          have hc := hM02 j.1 j.2
          have hsh : Shost j.1 = if (edgeOf j).1 < (edgeOf j).2 then {(edgeOf j).1, (edgeOf j).2} else ∅ := by
            dsimp only [Shost]; rw [← hj_eq, hShost_edge (edgeOf j).1 (edgeOf j).2]
          have hlt_ab : (edgeOf j).1 < (edgeOf j).2 := by
            by_contra hnl
            rw [hsh, if_neg hnl] at hc; simp at hc
          have hmemG : edgeOf j ∈ G := by
            have hjI := hXI (hM0X j.2)
            simp only [IG, Finset.mem_filter, Finset.mem_univ, true_and, hlt, ↓reduceDIte] at hjI
            exact hjI
          exact ⟨hlt_ab, by rwa [if_pos hlt_ab] at hsh, hmemG⟩
        let M : Finset (Fin m × Fin m) := M0.attach.image edgeOf
        have hinj : Set.InjOn edgeOf M0.attach := by
          intro j1 _ j2 _ heq
          by_contra hne
          have hne' : j1.1 ≠ j2.1 := fun h => hne (Subtype.ext h)
          have hd := hM0disj j1.1 j1.2 j2.1 j2.2 hne'
          rw [(hedge_spec j1).2.1, (hedge_spec j2).2.1, heq] at hd
          exact Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
        refine ⟨M, ?_, ?_, ?_, ?_⟩
        · intro e he
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
          exact (hedge_spec j).2.2
        · rw [Finset.card_image_of_injOn hinj, Finset.card_attach]; exact hM0_ge
        · intro e he
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
          exact (hedge_spec j).1
        · intro e he f hf hef
          obtain ⟨j1, _, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨j2, _, rfl⟩ := Finset.mem_image.mp hf
          have hne : j1.1 ≠ j2.1 := fun h => hef (by congr 1; exact Subtype.ext h)
          have hd := hM0disj j1.1 j1.2 j2.1 j2.2 hne
          rw [(hedge_spec j1).2.1, (hedge_spec j2).2.1] at hd
          convert hd
      · rintro ⟨M, hMG, hMcard, hMlt, hMdisj⟩
        obtain ⟨M', hM'M, hM'card⟩ := Finset.exists_subset_card_eq hMcard
        have hM'lt : ∀ e ∈ M', e.1 < e.2 := fun e he => hMlt e (hM'M he)
        have hM'disj : ∀ e ∈ M', ∀ f ∈ M', e ≠ f → Disjoint ({e.1, e.2} : Finset (Fin m)) {f.1, f.2} :=
          fun e he f hf hef => by convert hMdisj e (hM'M he) f (hM'M hf) hef
        let covV := M'.biUnion (fun e => ({e.1, e.2} : Finset (Fin m)))
        have hcovV_card : covV.card = 2 * M'.card := by
          convert matching_card_mul_two_le M' hM'lt (fun e he f hf hef => by convert hM'disj e he f hf hef)
        let XE : Finset (Fin (m * m + m)) := M'.image (fun e =>
          ⟨e.1.val * m + e.2.val, by
            have h1 : e.1.val + 1 ≤ m := e.1.isLt
            have h2 : e.2.val < m := e.2.isLt
            nlinarith⟩)
        let XV : Finset (Fin (m * m + m)) := (Finset.univ \ covV).image (fun v =>
          ⟨m * m + v.val, by omega⟩)
        refine ⟨XE ∪ XV, ?_, ?_, ?_⟩
        · refine Finset.union_subset ?_ ?_
          · intro j hj
            obtain ⟨e, heM', rfl⟩ := Finset.mem_image.mp hj
            have hlt : e.1.val * m + e.2.val < m * m := by
              have h1 : e.1.val + 1 ≤ m := e.1.isLt
              have h2 : e.2.val < m := e.2.isLt
              nlinarith
            simp only [IG, Finset.mem_filter, Finset.mem_univ, true_and, hlt, ↓reduceDIte]
            have hdiv : (e.1.val * m + e.2.val) / m = e.1.val := by
              rw [mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt e.2.isLt, Nat.add_zero]
            have hmod : (e.1.val * m + e.2.val) % m = e.2.val := by
              rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt e.2.isLt]
            have : (⟨(e.1.val * m + e.2.val) / m, by omega⟩, ⟨(e.1.val * m + e.2.val) % m, by omega⟩) = e := by
              ext <;> simp [hdiv, hmod]
            convert hMG (hM'M heM')
          · intro j hj
            obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
            simp only [IG, Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hlt : m * m + v.val < m * m
            · omega
            · simp [hlt]
        · have hXE_le : XE.card ≤ M'.card := Finset.card_image_le
          have hXV_le : XV.card ≤ (Finset.univ \ covV).card := Finset.card_image_le
          have hrem : (Finset.univ \ covV).card = m - 2 * M'.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
                Finset.card_univ, Fintype.card_fin, hcovV_card]
          have h2le : 2 * M'.card ≤ m := by
            rw [← hcovV_card]
            calc covV.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = m := by simp
          calc (XE ∪ XV).card ≤ XE.card + XV.card := Finset.card_union_le _ _
            _ ≤ M'.card + (m - 2 * M'.card) := Nat.add_le_add hXE_le (hrem ▸ hXV_le)
            _ ≤ m - t.val := by omega
        · ext v
          simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hv : v ∈ covV
          · simp only [covV, Finset.mem_biUnion] at hv
            obtain ⟨e, heM', hve⟩ := hv
            refine ⟨⟨e.1.val * m + e.2.val, by
              have h1 : e.1.val + 1 ≤ m := e.1.isLt
              have h2 : e.2.val < m := e.2.isLt
              nlinarith⟩, Or.inl (Finset.mem_image.mpr ⟨e, heM', rfl⟩), ?_⟩
            rw [hShost_edge e.1 e.2, if_pos (hM'lt e heM')]
            exact hve
          · refine ⟨⟨m * m + v.val, by omega⟩,
              Or.inr (Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩), ?_⟩
            rw [hShost_sing v]
            simp
