import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1480_aux
open PEqualNP.CircuitLowerBounds

noncomputable section

noncomputable local instance (priority := high) finDec {k : ℕ} : DecidableEq (Fin k) :=
  fun a b => Classical.propDecidable (a = b)

theorem fold_snoc {α β : Type} (F : List α → β → α) (xs : List α) (gs : List β) (g : β) :
    (gs ++ [g]).foldl (fun ts g => ts ++ [F ts g]) xs =
      gs.foldl (fun ts g => ts ++ [F ts g]) xs ++
        [F (gs.foldl (fun ts g => ts ++ [F ts g]) xs) g] := by
  simp [List.foldl_append]

theorem fold_length {α β : Type} (F : List α → β → α) (xs : List α) (gs : List β) :
    (gs.foldl (fun ts g => ts ++ [F ts g]) xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => rw [fold_snoc]; simp [ih]; omega

def infoF (k : ℕ) (ts : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) :
    Finset (Fin k) × Finset (Fin k) :=
  g.inputs.foldl (fun v t => let a := ts.getD t ((∅, ∅) : Finset (Fin k) × Finset (Fin k))
                             (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅)

def info0 (k : ℕ) : List (Finset (Fin k) × Finset (Fin k)) :=
  List.ofFn (fun j : Fin k => (({j}, ∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅, {j}) : Finset (Fin k) × Finset (Fin k))) ++ [(∅, ∅), (∅, ∅)]

def info (k : ℕ) (gs : List Gate) : List (Finset (Fin k) × Finset (Fin k)) :=
  gs.foldl (fun ts g => ts ++ [infoF k ts g]) (info0 k)

theorem info0_length (k : ℕ) : (info0 k).length = 2 * k + 2 := by
  simp [info0]; omega

theorem info_length (k : ℕ) (gs : List Gate) : (info k gs).length = 2 * k + 2 + gs.length := by
  rw [info, fold_length, info0_length]

theorem foldU_mono {k : ℕ} (ts : List (Finset (Fin k) × Finset (Fin k))) (l : List ℕ)
    (v : Finset (Fin k) × Finset (Fin k)) :
    (v.1 ⊆ (l.foldl (fun v t => let a := ts.getD t ((∅, ∅) : Finset (Fin k) × Finset (Fin k))
                             (v.1 ∪ a.1, v.2 ∪ a.2)) v).1 ∧
     v.2 ⊆ (l.foldl (fun v t => let a := ts.getD t ((∅, ∅) : Finset (Fin k) × Finset (Fin k))
                             (v.1 ∪ a.1, v.2 ∪ a.2)) v).2) ∧
    ∀ t ∈ l, (ts.getD t (∅, ∅)).1 ⊆ (l.foldl (fun v t => let a := ts.getD t ((∅, ∅) : Finset (Fin k) × Finset (Fin k))
                             (v.1 ∪ a.1, v.2 ∪ a.2)) v).1 ∧
      (ts.getD t (∅, ∅)).2 ⊆ (l.foldl (fun v t => let a := ts.getD t ((∅, ∅) : Finset (Fin k) × Finset (Fin k))
                             (v.1 ∪ a.1, v.2 ∪ a.2)) v).2 := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih (v.1 ∪ (ts.getD a (∅, ∅)).1, v.2 ∪ (ts.getD a (∅, ∅)).2)
    refine ⟨⟨Finset.subset_union_left.trans h1, Finset.subset_union_left.trans h2⟩, ?_⟩
    rintro t (rfl | ht)
    · exact ⟨Finset.subset_union_right.trans h1, Finset.subset_union_right.trans h2⟩
    · exact h3 t ht

theorem infoF_sub {k : ℕ} (ts : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) (t : ℕ)
    (ht : t ∈ g.inputs) :
    (ts.getD t (∅, ∅)).1 ⊆ (infoF k ts g).1 ∧ (ts.getD t (∅, ∅)).2 ⊆ (infoF k ts g).2 :=
  (foldU_mono ts g.inputs (∅, ∅)).2 t ht

theorem info0_x (k : ℕ) (i : Fin k) : (info0 k).getD i.val (∅, ∅) = ({i}, ∅) := by
  have h : i.val < (List.ofFn (fun j : Fin k => (({j}, ∅) : Finset (Fin k) × Finset (Fin k)))).length := by simp
  simp only [info0, List.append_assoc]
  rw [List.getD_append _ _ _ _ h]
  simp [List.getD_eq_getElem?_getD]

theorem info0_z (k : ℕ) (i : Fin k) : (info0 k).getD (k + i.val) (∅, ∅) = (∅, {i}) := by
  simp only [info0, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  have h : k + i.val - (List.ofFn (fun j : Fin k => (({j}, ∅) : Finset (Fin k) × Finset (Fin k)))).length
      < (List.ofFn (fun j : Fin k => ((∅, {j}) : Finset (Fin k) × Finset (Fin k)))).length := by simp
  rw [List.getD_append _ _ _ _ h]
  simp [List.getD_eq_getElem?_getD]

theorem info0_c (k : ℕ) (j : ℕ) (hj : 2 * k ≤ j) : (info0 k).getD j (∅, ∅) = (∅, ∅) := by
  simp only [info0, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_ofFn]
  rcases Nat.lt_or_ge (j - k - k) 2 with h | h
  · interval_cases h' : (j - k - k) <;> simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

def wires (gs : List Gate) (x : List Bool) : List Bool := (Circuit.mk gs 0).wires x

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = wires gs x ++ [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires, Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (x : List Bool) : (wires gs x).length = x.length + gs.length := by
  unfold wires Circuit.wires
  exact fold_length (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)) x gs

theorem mono_reach (k : ℕ) (gs : List Gate)
    (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hx : x.length = 2 * k + 2) (hy : y.length = 2 * k + 2)
    (hc : ∀ j, 2 * k ≤ j → x.getD j false = true → y.getD j false = true) :
    ∀ j, (∀ i ∈ ((info k gs).getD j (∅, ∅)).1, x.getD i.val false = true → y.getD i.val false = true) →
      (∀ i ∈ ((info k gs).getD j (∅, ∅)).2, x.getD (k + i.val) false = true →
        y.getD (k + i.val) false = true) →
      (wires gs x).getD j false = true → (wires gs y).getD j false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro j h1 h2 hv
    simp only [wires, Circuit.wires, List.foldl_nil] at hv ⊢
    simp only [info, List.foldl_nil] at h1 h2
    rcases Nat.lt_or_ge j k with hj | hj
    · have := h1 ⟨j, hj⟩ (by rw [info0_x k ⟨j, hj⟩]; simp)
      exact this hv
    · rcases Nat.lt_or_ge j (2 * k) with hj2 | hj2
      · have hjk : j - k < k := by omega
        have := h2 ⟨j - k, hjk⟩ (by
          have := info0_z k ⟨j - k, hjk⟩
          simp only at this
          rw [show k + (j - k) = j by omega] at this
          rw [this]; simp)
        simp only at this
        rw [show k + (j - k) = j by omega] at this
        exact this hv
      · exact hc j hj2 hv
  | append_singleton gs g ih =>
    have ih' := ih (fun g hg => hpos g (by simp [hg]))
    intro j h1 h2 hv
    rw [wires_snoc] at hv ⊢
    have hI : info k (gs ++ [g]) = info k gs ++ [infoF k (info k gs) g] := by
      unfold info; exact fold_snoc _ _ _ _
    rw [hI] at h1 h2
    have hlx := wires_length gs x
    have hly := wires_length gs y
    have hli := info_length k gs
    rcases Nat.lt_trichotomy j (2 * k + 2 + gs.length) with hj | hj | hj
    · rw [List.getD_append _ _ _ _ (by omega)] at hv ⊢ h1 h2
      exact ih' j h1 h2 hv
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hv ⊢ h1 h2
      have e1 : j - (wires gs x).length = 0 := by omega
      have e2 : j - (wires gs y).length = 0 := by omega
      have e3 : j - (info k gs).length = 0 := by omega
      rw [e1] at hv; rw [e2]; rw [e3] at h1 h2
      simp only [List.getD_cons_zero] at hv ⊢ h1 h2
      have key : ∀ t ∈ g.inputs, (wires gs x).getD t false = true → (wires gs y).getD t false = true := by
        intro t ht
        obtain ⟨s1, s2⟩ := infoF_sub (info k gs) g t ht
        exact ih' t (fun i hi => h1 i (s1 hi)) (fun i hi => h2 i (s2 hi))
      rcases hpos g (by simp) with ho | ho
      · rw [ho] at hv ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv ⊢
        exact fun t ht => key t ht (hv t ht)
      · rw [ho] at hv ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv ⊢
        obtain ⟨t, ht, hvt⟩ := hv
        exact ⟨t, ht, key t ht hvt⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
      exact absurd hv (by simp)

noncomputable def word {k : ℕ} (ones zeros : Finset (Fin k)) : List Bool :=
  List.ofFn (fun j : Fin k => @decide (j ∈ ones) (Classical.propDecidable _)) ++
  List.ofFn (fun j : Fin k => @decide (j ∈ zeros) (Classical.propDecidable _)) ++ [false, true]

theorem word_length {k : ℕ} (I O : Finset (Fin k)) : (word I O).length = 2 * k + 2 := by
  simp [word]; omega

theorem word_x {k : ℕ} (I O : Finset (Fin k)) (i : Fin k) :
    ((word I O).getD i.val false = true ↔ i ∈ I) := by
  have h : i.val < (List.ofFn (fun j : Fin k => @decide (j ∈ I) (Classical.propDecidable _))).length := by simp
  simp only [word, List.append_assoc]
  rw [List.getD_append _ _ _ _ h]
  simp [List.getD_eq_getElem?_getD]

theorem word_z {k : ℕ} (I O : Finset (Fin k)) (i : Fin k) :
    ((word I O).getD (k + i.val) false = true ↔ i ∈ O) := by
  simp only [word, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  have h : k + i.val - (List.ofFn (fun j : Fin k => @decide (j ∈ I) (Classical.propDecidable _))).length
      < (List.ofFn (fun j : Fin k => @decide (j ∈ O) (Classical.propDecidable _))).length := by simp
  rw [List.getD_append _ _ _ _ h]
  simp [List.getD_eq_getElem?_getD]

theorem word_c {k : ℕ} (I O I' O' : Finset (Fin k)) (j : ℕ) (hj : 2 * k ≤ j) :
    (word I O).getD j false = (word I' O').getD j false := by
  simp only [word, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp

theorem mono_word (k : ℕ) (gs : List Gate)
    (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (I O I' O' : Finset (Fin k)) (j : ℕ)
    (h1 : ∀ i ∈ ((info k gs).getD j (∅, ∅)).1, i ∈ I → i ∈ I')
    (h2 : ∀ i ∈ ((info k gs).getD j (∅, ∅)).2, i ∈ O → i ∈ O')
    (hv : (wires gs (word I O)).getD j false = true) :
    (wires gs (word I' O')).getD j false = true := by
  refine mono_reach k gs hpos (word I O) (word I' O') (word_length _ _) (word_length _ _) ?_ j ?_ ?_ hv
  · intro j hj h; rw [← word_c I O I' O' j hj]; exact h
  · intro i hi h; exact (word_x I' O' i).2 (h1 i hi ((word_x I O i).1 h))
  · intro i hi h; exact (word_z I' O' i).2 (h2 i hi ((word_z I O i).1 h))

theorem merge (k : ℕ) (gs : List Gate)
    (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (Xa Xb : Finset (Fin k))
    (hagree : ∀ i, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∧ i ∈ ((info k gs).getD b (∅, ∅)).2) ∨
        (i ∈ ((info k gs).getD a (∅, ∅)).2 ∧ i ∈ ((info k gs).getD b (∅, ∅)).1) → (i ∈ Xa ↔ i ∈ Xb))
    (ha : (wires gs (word Xa (Finset.univ \ Xa))).getD a false = true)
    (hb : (wires gs (word Xb (Finset.univ \ Xb))).getD b false = true) :
    ∃ X : Finset (Fin k), (∀ i, (i ∈ X ↔ i ∈ Xa) ∨ (i ∈ X ↔ i ∈ Xb)) ∧
      (wires gs (word X (Finset.univ \ X))).getD a false = true ∧
      (wires gs (word X (Finset.univ \ X))).getD b false = true := by
  classical
  refine ⟨Finset.univ.filter (fun i => (i ∈ ((info k gs).getD a (∅, ∅)).1 ∧ i ∈ Xa) ∨
      (i ∈ ((info k gs).getD b (∅, ∅)).1 ∧ i ∈ Xb) ∨ (i ∈ Xa ∧ i ∈ Xb)), ?_, ?_, ?_⟩
  · intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : i ∈ Xa <;> by_cases h2 : i ∈ Xb <;> simp only [h1, h2] <;> tauto
  · refine mono_word k gs hpos _ _ _ _ a ?_ ?_ ha
    · intro i hi hX
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨hi, hX⟩
    · intro i hi hX
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter] at hX ⊢
      rintro (⟨_, h⟩ | ⟨h, h'⟩ | ⟨h, _⟩)
      · exact hX h
      · exact hX ((hagree i (Or.inr ⟨hi, h⟩)).2 h')
      · exact hX h
  · refine mono_word k gs hpos _ _ _ _ b ?_ ?_ hb
    · intro i hi hX
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr (Or.inl ⟨hi, hX⟩)
    · intro i hi hX
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter] at hX ⊢
      rintro (⟨h, h'⟩ | ⟨_, h⟩ | ⟨_, h⟩)
      · exact hX ((hagree i (Or.inl ⟨h, hi⟩)).1 h')
      · exact hX h
      · exact hX h

def W {k : ℕ} (gs : List Gate) (X : Finset (Fin k)) (j : ℕ) : Prop :=
  (wires gs (word X (Finset.univ \ X))).getD j false = true

def Fits {k : ℕ} (X I O : Finset (Fin k)) : Prop := (∀ i, i ∈ X → i ∈ I) ∧ (∀ i, i ∉ X → i ∈ O)

theorem fits_iff {k : ℕ} (X I O : Finset (Fin k)) :
    Fits X I O ↔ (X ⊆ I ∧ Finset.univ \ X ⊆ O) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i hi, fun i hi => h2 i (by simpa using hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 hi, fun i hi => h2 (by simpa using hi)⟩

def Lit {k : ℕ} (τ U I O : Finset (Fin k)) : Prop := ∀ i ∈ U, (i ∈ τ → i ∈ I) ∧ (i ∉ τ → i ∈ O)

theorem W_mono (k : ℕ) (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X X' : Finset (Fin k)) (j : ℕ)
    (h1 : ∀ i ∈ ((info k gs).getD j (∅, ∅)).1, i ∈ X → i ∈ X')
    (h2 : ∀ i ∈ ((info k gs).getD j (∅, ∅)).2, i ∉ X → i ∉ X')
    (hv : W gs X j) : W gs X' j := by
  refine mono_word k gs hpos _ _ _ _ j h1 ?_ hv
  intro i hi h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at h ⊢
  exact h2 i hi h

theorem restrict_sem (k : ℕ) (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a : ℕ) (I O τ U : Finset (Fin k)) :
    (∃ X, Fits X I O ∧ (∀ i ∈ U, (i ∈ X ↔ i ∈ τ)) ∧ W gs X a) ↔
      (Lit τ U I O ∧ ∃ X, Fits X I O ∧
        (∀ i ∈ U, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∨ i ∈ ((info k gs).getD a (∅, ∅)).2) →
          (i ∈ X ↔ i ∈ τ)) ∧ W gs X a) := by
  classical
  constructor
  · rintro ⟨X, ⟨f1, f2⟩, hag, hw⟩
    refine ⟨fun i hi => ⟨fun h => f1 i ((hag i hi).2 h), fun h => f2 i (fun h' => h ((hag i hi).1 h'))⟩,
      X, ⟨f1, f2⟩, fun i hi _ => hag i hi, hw⟩
  · rintro ⟨hl, X, ⟨f1, f2⟩, hag, hw⟩
    refine ⟨Finset.univ.filter (fun i => (i ∈ U ∧ i ∈ τ) ∨ (i ∉ U ∧ i ∈ X)), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact (hl i h1).1 h2
      · exact f1 i h2
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hU : i ∈ U
      · exact (hl i hU).2 (fun h => hi (Or.inl ⟨hU, h⟩))
      · exact f2 i (fun h => hi (Or.inr ⟨hU, h⟩))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · refine W_mono k gs hpos X _ a ?_ ?_ hw
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hU : i ∈ U
        · exact Or.inl ⟨hU, (hag i hU (Or.inl hi)).1 hX⟩
        · exact Or.inr ⟨hU, hX⟩
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨hU, h⟩ | ⟨_, h⟩)
        · exact hX ((hag i hU (Or.inr hi)).2 h)
        · exact hX h

theorem and_sem (k : ℕ) (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (I O τ U : Finset (Fin k))
    (hU : ∀ i, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∧ i ∈ ((info k gs).getD b (∅, ∅)).2) ∨
        (i ∈ ((info k gs).getD a (∅, ∅)).2 ∧ i ∈ ((info k gs).getD b (∅, ∅)).1) → i ∈ U) :
    (∃ X, Fits X I O ∧ (∀ i ∈ U, (i ∈ X ↔ i ∈ τ)) ∧ W gs X a ∧ W gs X b) ↔
      (Lit τ U I O ∧
        (∃ X, Fits X I O ∧
          (∀ i ∈ U, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∨ i ∈ ((info k gs).getD a (∅, ∅)).2) →
            (i ∈ X ↔ i ∈ τ)) ∧ W gs X a) ∧
        (∃ X, Fits X I O ∧
          (∀ i ∈ U, (i ∈ ((info k gs).getD b (∅, ∅)).1 ∨ i ∈ ((info k gs).getD b (∅, ∅)).2) →
            (i ∈ X ↔ i ∈ τ)) ∧ W gs X b)) := by
  classical
  constructor
  · rintro ⟨X, ⟨f1, f2⟩, hag, hwa, hwb⟩
    exact ⟨fun i hi => ⟨fun h => f1 i ((hag i hi).2 h), fun h => f2 i (fun h' => h ((hag i hi).1 h'))⟩,
      ⟨X, ⟨f1, f2⟩, fun i hi _ => hag i hi, hwa⟩, ⟨X, ⟨f1, f2⟩, fun i hi _ => hag i hi, hwb⟩⟩
  · rintro ⟨hl, ⟨Xa, ⟨fa1, fa2⟩, haga, hwa⟩, ⟨Xb, ⟨fb1, fb2⟩, hagb, hwb⟩⟩
    refine ⟨Finset.univ.filter (fun i => (i ∈ U ∧ i ∈ τ) ∨ (i ∉ U ∧
      ((i ∈ ((info k gs).getD a (∅, ∅)).1 ∧ i ∈ Xa) ∨ (i ∈ ((info k gs).getD b (∅, ∅)).1 ∧ i ∈ Xb) ∨
        (i ∈ Xa ∧ i ∈ Xb)))), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨h1, h2⟩ | ⟨_, ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h2, _⟩⟩
      · exact (hl i h1).1 h2
      · exact fa1 i h2
      · exact fb1 i h2
      · exact fa1 i h2
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hUi : i ∈ U
      · exact (hl i hUi).2 (fun h => hi (Or.inl ⟨hUi, h⟩))
      · by_cases hXa : i ∈ Xa
        · exact fb2 i (fun h => hi (Or.inr ⟨hUi, Or.inr (Or.inr ⟨hXa, h⟩)⟩))
        · exact fa2 i hXa
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · refine W_mono k gs hpos Xa _ a ?_ ?_ hwa
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hUi : i ∈ U
        · exact Or.inl ⟨hUi, (haga i hUi (Or.inl hi)).1 hX⟩
        · exact Or.inr ⟨hUi, Or.inl ⟨hi, hX⟩⟩
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨hUi, h⟩ | ⟨hUi, ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩⟩)
        · exact hX ((haga i hUi (Or.inr hi)).2 h)
        · exact hX h
        · exact hUi (hU i (Or.inr ⟨hi, h⟩))
        · exact hX h
    · refine W_mono k gs hpos Xb _ b ?_ ?_ hwb
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hUi : i ∈ U
        · exact Or.inl ⟨hUi, (hagb i hUi (Or.inl hi)).1 hX⟩
        · exact Or.inr ⟨hUi, Or.inr (Or.inl ⟨hi, hX⟩)⟩
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨hUi, h⟩ | ⟨hUi, ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩)
        · exact hX ((hagb i hUi (Or.inr hi)).2 h)
        · exact hUi (hU i (Or.inl ⟨h, hi⟩))
        · exact hX h
        · exact hX h

theorem wires_prefix (gs gs' : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length + gs.length) :
    (wires (gs ++ gs') x).getD j false = (wires gs x).getD j false := by
  induction gs' using List.reverseRecOn with
  | nil => simp
  | append_singleton gs' g ih =>
    rw [← List.append_assoc, wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length]; simp; omega), ih]

theorem info_prefix (k : ℕ) (gs gs' : List Gate) (j : ℕ) (hj : j < 2 * k + 2 + gs.length) :
    (info k (gs ++ gs')).getD j (∅, ∅) = (info k gs).getD j (∅, ∅) := by
  induction gs' using List.reverseRecOn with
  | nil => simp
  | append_singleton gs' g ih =>
    have hI : info k (gs ++ gs' ++ [g]) = info k (gs ++ gs') ++ [infoF k (info k (gs ++ gs')) g] := by
      unfold info; exact fold_snoc _ _ _ _
    rw [← List.append_assoc, hI, List.getD_append _ _ _ _ (by rw [info_length]; simp; omega), ih]

theorem wires_input (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (wires gs x).getD j false = x.getD j false := by
  have := wires_prefix [] gs x j (by simpa using hj)
  simpa [wires, Circuit.wires] using this

theorem input_sem (k : ℕ) (gs : List Gate) (I O : Finset (Fin k)) (hIO : I ∪ O = Finset.univ)
    (j : ℕ) (hj : j < 2 * k + 2) :
    ((word I O).getD j false = true ↔ ∃ X, Fits X I O ∧ W gs X j) := by
  classical
  have hmem : ∀ i : Fin k, i ∈ I ∨ i ∈ O := fun i => by
    have : i ∈ I ∪ O := by rw [hIO]; exact Finset.mem_univ i
    simpa using this
  unfold W
  have hin : ∀ A B : Finset (Fin k), (wires gs (word A B)).getD j false = (word A B).getD j false :=
    fun A B => wires_input gs _ j (by rw [word_length]; exact hj)
  simp only [hin]
  rcases Nat.lt_or_ge j k with h | h
  · have e := fun (A B : Finset (Fin k)) => word_x A B ⟨j, h⟩
    simp only at e
    rw [e]
    constructor
    · intro hI
      refine ⟨I, ⟨fun i hi => hi, fun i hi => (hmem i).resolve_left hi⟩, ?_⟩
      rw [e]; exact hI
    · rintro ⟨X, ⟨f1, _⟩, hX⟩
      rw [e] at hX; exact f1 _ hX
  · rcases Nat.lt_or_ge j (2 * k) with h2 | h2
    · have hjk : j - k < k := by omega
      have e := fun (A B : Finset (Fin k)) => word_z A B ⟨j - k, hjk⟩
      simp only at e
      rw [show k + (j - k) = j by omega] at e
      rw [e]
      constructor
      · intro hO
        refine ⟨Finset.univ \ O, ⟨fun i hi => (hmem i).resolve_right (by simpa using hi),
          fun i hi => by simpa using hi⟩, ?_⟩
        rw [e]; simpa using hO
      · rintro ⟨X, ⟨_, f2⟩, hX⟩
        rw [e] at hX
        exact f2 _ (by simpa using hX)
    · constructor
      · intro hv
        refine ⟨I, ⟨fun i hi => hi, fun i hi => (hmem i).resolve_left hi⟩, ?_⟩
        rw [word_c I (Finset.univ \ I) I O j h2]; exact hv
      · rintro ⟨X, _, hX⟩
        rw [word_c X (Finset.univ \ X) I O j h2] at hX; exact hX

theorem gate_val (A B : List Gate) (g : Gate) (x : List Bool)
    (hrb : ∀ i ∈ g.inputs, i < x.length + A.length) :
    (wires (A ++ [g] ++ B) x).getD (x.length + A.length) false =
      g.op.eval (g.inputs.map fun i => (wires (A ++ [g] ++ B) x).getD i false) := by
  rw [wires_prefix (A ++ [g]) B x _ (by simp), wires_snoc,
    List.getD_append_right _ _ _ _ (by rw [wires_length])]
  have e : x.length + A.length - (wires A x).length = 0 := by rw [wires_length]; omega
  rw [e, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hrb i hi
  rw [wires_prefix (A ++ [g]) B x i (by simp; omega), wires_snoc,
    List.getD_append _ _ _ _ (by rw [wires_length]; omega)]

theorem info_gate (k : ℕ) (A B : List Gate) (g : Gate) :
    (info k (A ++ [g] ++ B)).getD (2 * k + 2 + A.length) (∅, ∅) = infoF k (info k A) g := by
  have hI : info k (A ++ [g]) = info k A ++ [infoF k (info k A) g] := by
    unfold info; exact fold_snoc _ _ _ _
  rw [info_prefix k (A ++ [g]) B _ (by simp), hI,
    List.getD_append_right _ _ _ _ (by rw [info_length])]
  have e : 2 * k + 2 + A.length - (info k A).length = 0 := by rw [info_length]; omega
  rw [e, List.getD_cons_zero]

theorem info_gate_sub (k : ℕ) (A B : List Gate) (g : Gate) (i : ℕ) (hi : i ∈ g.inputs)
    (hlt : i < 2 * k + 2 + A.length) :
    ((info k (A ++ [g] ++ B)).getD i (∅, ∅)).1 ⊆
        ((info k (A ++ [g] ++ B)).getD (2 * k + 2 + A.length) (∅, ∅)).1 ∧
      ((info k (A ++ [g] ++ B)).getD i (∅, ∅)).2 ⊆
        ((info k (A ++ [g] ++ B)).getD (2 * k + 2 + A.length) (∅, ∅)).2 := by
  rw [info_gate, List.append_assoc, info_prefix k A ([g] ++ B) i hlt]
  exact infoF_sub (info k A) g i hi

def Sem {k : ℕ} (gs : List Gate) (I O U τ : Finset (Fin k)) (a : ℕ) : Prop :=
  ∃ X, Fits X I O ∧ (∀ i ∈ U, (i ∈ X ↔ i ∈ τ)) ∧ W gs X a

theorem ext_sem (k : ℕ) (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a : ℕ) (I O τ U : Finset (Fin k)) (v : Fin k)
    (hv1 : v ∉ ((info k gs).getD a (∅, ∅)).1) (hv2 : v ∉ ((info k gs).getD a (∅, ∅)).2) :
    Sem gs I O (insert v U) τ a ↔ (((v ∈ τ → v ∈ I) ∧ (v ∉ τ → v ∈ O)) ∧ Sem gs I O U τ a) := by
  classical
  constructor
  · rintro ⟨X, ⟨f1, f2⟩, hag, hw⟩
    have hvv := hag v (Finset.mem_insert_self v U)
    exact ⟨⟨fun h => f1 v (hvv.2 h), fun h => f2 v (fun h' => h (hvv.1 h'))⟩,
      X, ⟨f1, f2⟩, fun i hi => hag i (Finset.mem_insert_of_mem hi), hw⟩
  · rintro ⟨⟨l1, l2⟩, X, ⟨f1, f2⟩, hag, hw⟩
    refine ⟨Finset.univ.filter (fun i => (i = v ∧ i ∈ τ) ∨ (i ≠ v ∧ i ∈ X)), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨rfl, h⟩ | ⟨_, h⟩
      · exact l1 h
      · exact f1 i h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hiv : i = v
      · subst hiv; exact l2 (fun h => hi (Or.inl ⟨rfl, h⟩))
      · exact f2 i (fun h => hi (Or.inr ⟨hiv, h⟩))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simp
      · have := hag i hi'
        by_cases hiv : i = v
        · subst hiv; simp
        · simp [hiv, this]
    · refine W_mono k gs hpos X _ a ?_ ?_ hw
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨fun h => hv1 (h ▸ hi), hX⟩
      · intro i hi hX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hv2 (h ▸ hi)
        · exact hX h

theorem elim_sem (k : ℕ) (gs : List Gate) (a : ℕ) (I O τ U : Finset (Fin k)) (v : Fin k)
    (hv : v ∉ U) :
    Sem gs I O U τ a ↔
      (Sem gs I O (insert v U) (τ.erase v) a ∨ Sem gs I O (insert v U) (insert v τ) a) := by
  classical
  constructor
  · rintro ⟨X, hf, hag, hw⟩
    by_cases hX : v ∈ X
    · refine Or.inr ⟨X, hf, ?_, hw⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simp [hX]
      · have hne : i ≠ v := fun h => hv (h ▸ hi')
        simp [hne, hag i hi']
    · refine Or.inl ⟨X, hf, ?_, hw⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simp [hX]
      · have hne : i ≠ v := fun h => hv (h ▸ hi')
        simp [hne, hag i hi']
  · rintro (⟨X, hf, hag, hw⟩ | ⟨X, hf, hag, hw⟩)
    · refine ⟨X, hf, ?_, hw⟩
      intro i hi
      have hne : i ≠ v := fun h => hv (h ▸ hi)
      have := hag i (Finset.mem_insert_of_mem hi)
      simpa [hne] using this
    · refine ⟨X, hf, ?_, hw⟩
      intro i hi
      have hne : i ≠ v := fun h => hv (h ▸ hi)
      have := hag i (Finset.mem_insert_of_mem hi)
      simpa [hne] using this

theorem and_comb (k : ℕ) (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (I O τ U : Finset (Fin k))
    (hU : ∀ i, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∧ i ∈ ((info k gs).getD b (∅, ∅)).2) ∨
        (i ∈ ((info k gs).getD a (∅, ∅)).2 ∧ i ∈ ((info k gs).getD b (∅, ∅)).1) → i ∈ U) :
    (∃ X, Fits X I O ∧ (∀ i ∈ U, (i ∈ X ↔ i ∈ τ)) ∧ W gs X a ∧ W gs X b) ↔
      (Sem gs I O U τ a ∧ Sem gs I O U τ b) := by
  unfold Sem
  rw [and_sem k gs hpos a b I O τ U hU, restrict_sem k gs hpos a, restrict_sem k gs hpos b]
  tauto

theorem or_comb (k : ℕ) (gs : List Gate) (a b : ℕ) (I O τ U : Finset (Fin k)) :
    (∃ X, Fits X I O ∧ (∀ i ∈ U, (i ∈ X ↔ i ∈ τ)) ∧ (W gs X a ∨ W gs X b)) ↔
      (Sem gs I O U τ a ∨ Sem gs I O U τ b) := by
  unfold Sem
  constructor
  · rintro ⟨X, hf, hag, h | h⟩
    · exact Or.inl ⟨X, hf, hag, h⟩
    · exact Or.inr ⟨X, hf, hag, h⟩
  · rintro (⟨X, hf, hag, h⟩ | ⟨X, hf, hag, h⟩)
    · exact ⟨X, hf, hag, Or.inl h⟩
    · exact ⟨X, hf, hag, Or.inr h⟩

def depF (ts : List ℕ) (g : Gate) : ℕ := 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0

def dep (n : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun ts g => ts ++ [depF ts g]) (List.replicate n 0)

theorem dep_length (n : ℕ) (gs : List Gate) : (dep n gs).length = n + gs.length := by
  rw [dep, fold_length]; simp

theorem dep_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    dep n (gs ++ [g]) = dep n gs ++ [depF (dep n gs) g] := by
  unfold dep; exact fold_snoc _ _ _ _

theorem dep_prefix (n : ℕ) (gs gs' : List Gate) (j : ℕ) (hj : j < n + gs.length) :
    (dep n (gs ++ gs')).getD j 0 = (dep n gs).getD j 0 := by
  induction gs' using List.reverseRecOn with
  | nil => simp
  | append_singleton gs' g ih =>
    rw [← List.append_assoc, dep_snoc, List.getD_append _ _ _ _ (by rw [dep_length]; simp; omega), ih]

theorem dep_input (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < n) : (dep n gs).getD j 0 = 0 := by
  have := dep_prefix n [] gs j (by simpa using hj)
  rw [List.nil_append] at this
  rw [this]
  simp [dep, List.getD_eq_getElem?_getD]

theorem dep_gate (n : ℕ) (A B : List Gate) (g : Gate) :
    (dep n (A ++ [g] ++ B)).getD (n + A.length) 0 = depF (dep n A) g := by
  rw [dep_prefix n (A ++ [g]) B _ (by simp), dep_snoc,
    List.getD_append_right _ _ _ _ (by rw [dep_length])]
  have e : n + A.length - (dep n A).length = 0 := by rw [dep_length]; omega
  rw [e, List.getD_cons_zero]

theorem foldmax_le (ts : List ℕ) (l : List ℕ) (d m : ℕ) (hm : m ≤ d)
    (h : ∀ i ∈ l, ts.getD i 0 ≤ d) : l.foldl (fun m j => max m (ts.getD j 0)) m ≤ d := by
  induction l generalizing m with
  | nil => simpa using hm
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact ih _ (max_le hm (h a (by simp))) (fun i hi => h i (by simp [hi]))

theorem depF_le (ts : List ℕ) (g : Gate) (d : ℕ) (h : ∀ i ∈ g.inputs, ts.getD i 0 ≤ d) :
    depF ts g ≤ 1 + d := by
  unfold depF
  have := foldmax_le ts g.inputs d 0 (Nat.zero_le _) h
  omega

theorem block_val (es new : List Gate) (x : List Bool)
    (hrb : ∀ g ∈ new, ∀ i ∈ g.inputs, i < x.length + es.length) (m : ℕ) (hm : m < new.length) :
    (wires (es ++ new) x).getD (x.length + es.length + m) false =
      new[m].op.eval (new[m].inputs.map fun i => (wires es x).getD i false) := by
  have hsplit : es ++ new = (es ++ new.take m) ++ [new[m]] ++ new.drop (m + 1) := by
    simp [List.append_assoc]
  have hlen : (es ++ new.take m).length = es.length + m := by
    simp [List.length_take]; omega
  have hin := hrb new[m] (List.getElem_mem hm)
  have h := gate_val (es ++ new.take m) (new.drop (m + 1)) new[m] x
    (fun i hi => by rw [hlen]; have := hin i hi; omega)
  rw [hlen, ← Nat.add_assoc, ← hsplit] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact wires_prefix es new x i (hin i hi)

theorem block_dep (n : ℕ) (es new : List Gate)
    (hrb : ∀ g ∈ new, ∀ i ∈ g.inputs, i < n + es.length) (m : ℕ) (hm : m < new.length) (d : ℕ)
    (hd : ∀ i ∈ new[m].inputs, (dep n es).getD i 0 ≤ d) :
    (dep n (es ++ new)).getD (n + es.length + m) 0 ≤ 1 + d := by
  have hsplit : es ++ new = (es ++ new.take m) ++ [new[m]] ++ new.drop (m + 1) := by
    simp [List.append_assoc]
  have hlen : (es ++ new.take m).length = es.length + m := by
    simp [List.length_take]; omega
  have hin := hrb new[m] (List.getElem_mem hm)
  have h := dep_gate n (es ++ new.take m) (new.drop (m + 1)) new[m]
  rw [hlen, ← Nat.add_assoc, ← hsplit] at h
  rw [h]
  apply depF_le
  intro i hi
  rw [dep_prefix n es (new.take m) i (hin i hi)]
  exact hd i hi

noncomputable def subs {k : ℕ} (U : Finset (Fin k)) : List (Finset (Fin k)) := U.powerset.toList

theorem subs_length {k : ℕ} (U : Finset (Fin k)) : (subs U).length = 2 ^ U.card := by
  simp [subs]

noncomputable def blockIdx {k : ℕ} (U : Finset (Fin k)) (es : List Gate) (τ : Finset (Fin k)) : ℕ :=
  2 * k + 2 + es.length + (subs U).idxOf (τ ∩ U)

theorem block_spec {k : ℕ} (es : List Gate) (U : Finset (Fin k)) (mk : Finset (Fin k) → Gate)
    (hrb : ∀ τ, ∀ i ∈ (mk τ).inputs, i < 2 * k + 2 + es.length) (τ : Finset (Fin k)) :
    blockIdx U es τ < 2 * k + 2 + (es ++ (subs U).map mk).length ∧
    (∀ I O : Finset (Fin k), (wires (es ++ (subs U).map mk) (word I O)).getD (blockIdx U es τ) false =
      (mk (τ ∩ U)).op.eval ((mk (τ ∩ U)).inputs.map fun i => (wires es (word I O)).getD i false)) ∧
    ∀ d, (∀ i ∈ (mk (τ ∩ U)).inputs, (dep (2 * k + 2) es).getD i 0 ≤ d) →
      (dep (2 * k + 2) (es ++ (subs U).map mk)).getD (blockIdx U es τ) 0 ≤ 1 + d := by
  have hmem : τ ∩ U ∈ subs U := by simp [subs, Finset.mem_powerset]
  have hm : (subs U).idxOf (τ ∩ U) < ((subs U).map mk).length := by
    rw [List.length_map]; exact List.idxOf_lt_length_of_mem hmem
  have hget : ((subs U).map mk)[(subs U).idxOf (τ ∩ U)] = mk (τ ∩ U) := by
    simp [List.getElem_map]
  have hrb' : ∀ g ∈ (subs U).map mk, ∀ i ∈ g.inputs, i < 2 * k + 2 + es.length := by
    intro g hg
    obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hg
    exact hrb σ
  refine ⟨?_, ?_, ?_⟩
  · unfold blockIdx; rw [List.length_append]; omega
  · intro I O
    have h := block_val es ((subs U).map mk) (word I O) (by rw [word_length]; exact hrb') _ hm
    rw [word_length, hget] at h
    exact h
  · intro d hd
    have h := block_dep (2 * k + 2) es ((subs U).map mk) hrb' _ hm d (by rw [hget]; exact hd)
    exact h

def Tab {k : ℕ} (gs es : List Gate) (U : Finset (Fin k)) (a d : ℕ) (f : Finset (Fin k) → ℕ) : Prop :=
  ∀ τ, f τ < 2 * k + 2 + es.length ∧ (dep (2 * k + 2) es).getD (f τ) 0 ≤ d ∧
    ∀ I O : Finset (Fin k), I ∪ O = Finset.univ →
      ((wires es (word I O)).getD (f τ) false = true ↔ Sem gs I O U τ a)

theorem tab_append {k : ℕ} (gs es new : List Gate) (U : Finset (Fin k)) (a d : ℕ)
    (f : Finset (Fin k) → ℕ) (h : Tab gs es U a d f) : Tab gs (es ++ new) U a d f := by
  intro τ
  obtain ⟨h1, h2, h3⟩ := h τ
  refine ⟨by rw [List.length_append]; omega, by rw [dep_prefix _ _ _ _ h1]; exact h2, ?_⟩
  intro I O hIO
  rw [wires_prefix es new _ _ (by rw [word_length]; exact h1)]
  exact h3 I O hIO

theorem tab_mono {k : ℕ} (gs es : List Gate) (U : Finset (Fin k)) (a d d' : ℕ) (hd : d ≤ d')
    (f : Finset (Fin k) → ℕ) (h : Tab gs es U a d f) : Tab gs es U a d' f := by
  intro τ
  obtain ⟨h1, h2, h3⟩ := h τ
  exact ⟨h1, h2.trans hd, h3⟩

theorem sem_inter {k : ℕ} (gs : List Gate) (I O U τ : Finset (Fin k)) (a : ℕ) :
    Sem gs I O U (τ ∩ U) a ↔ Sem gs I O U τ a := by
  unfold Sem
  constructor
  · rintro ⟨X, hf, hag, hw⟩
    exact ⟨X, hf, fun i hi => by have := hag i hi; simpa [hi] using this, hw⟩
  · rintro ⟨X, hf, hag, hw⟩
    exact ⟨X, hf, fun i hi => by have := hag i hi; simpa [hi] using this, hw⟩

theorem tab_elim {k : ℕ} (gs es : List Gate) (U : Finset (Fin k)) (v : Fin k) (hv : v ∉ U)
    (a d : ℕ) (f : Finset (Fin k) → ℕ) (h : Tab gs es (insert v U) a d f) :
    Tab gs (es ++ (subs U).map fun τ => ⟨GateOp.or, [f (τ.erase v), f (insert v τ)]⟩) U a (1 + d)
      (blockIdx U es) := by
  intro τ
  obtain ⟨b1, b2, b3⟩ := block_spec es U (fun τ => ⟨GateOp.or, [f (τ.erase v), f (insert v τ)]⟩)
    (by intro σ i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact (h _).1
        · exact (h _).1) τ
  refine ⟨b1, b3 d (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact (h _).2.1
    · exact (h _).2.1), ?_⟩
  intro I O hIO
  rw [b2 I O, ← sem_inter, elim_sem k gs a I O (τ ∩ U) U v hv,
    ← (h ((τ ∩ U).erase v)).2.2 I O hIO, ← (h (insert v (τ ∩ U))).2.2 I O hIO]
  simp [GateOp.eval]

theorem tab_ext {k : ℕ} (gs es : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (U : Finset (Fin k)) (v : Fin k)
    (a d : ℕ) (hv1 : v ∉ ((info k gs).getD a (∅, ∅)).1) (hv2 : v ∉ ((info k gs).getD a (∅, ∅)).2)
    (f : Finset (Fin k) → ℕ) (h : Tab gs es U a d f) :
    Tab gs (es ++ (subs (insert v U)).map fun τ =>
        ⟨GateOp.and, [f τ, if v ∈ τ then v.val else k + v.val]⟩) (insert v U) a (1 + d)
      (blockIdx (insert v U) es) := by
  classical
  have hlit : ∀ σ : Finset (Fin k), (if v ∈ σ then v.val else k + v.val) < 2 * k + 2 := by
    intro σ; split <;> omega
  intro τ
  obtain ⟨b1, b2, b3⟩ := block_spec es (insert v U)
    (fun τ => ⟨GateOp.and, [f τ, if v ∈ τ then v.val else k + v.val]⟩)
    (by intro σ i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact (h _).1
        · have := hlit σ; omega) τ
  refine ⟨b1, b3 d (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact (h _).2.1
    · rw [dep_input _ _ _ (hlit _)]; exact Nat.zero_le _), ?_⟩
  intro I O hIO
  rw [b2 I O, ← sem_inter, ext_sem k gs hpos a I O (τ ∩ insert v U) U v hv1 hv2,
    ← (h (τ ∩ insert v U)).2.2 I O hIO]
  have hin : (wires es (word I O)).getD (if v ∈ τ ∩ insert v U then v.val else k + v.val) false
      = (word I O).getD (if v ∈ τ ∩ insert v U then v.val else k + v.val) false :=
    wires_input es _ _ (by rw [word_length]; exact hlit _)
  have hI : ∀ i : Fin k, i ∈ I ∨ i ∈ O := fun i => by
    have : i ∈ I ∪ O := by rw [hIO]; exact Finset.mem_univ i
    simpa using this
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, id, hin]
  by_cases hvτ : v ∈ τ ∩ insert v U
  · simp only [hvτ, ite_true, word_x, not_true, false_imp_iff, and_true, forall_true_left]
    tauto
  · simp only [hvτ, ite_false, word_z, not_false_iff, forall_true_left, false_imp_iff, true_and]
    tauto

def Good (k : ℕ) (es : List Gate) : Prop :=
  (∀ g ∈ es, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < es.length, ∀ i ∈ (es.getD j ⟨GateOp.or, []⟩).inputs, i < 2 * k + 2 + j

theorem good_append (k : ℕ) (es new : List Gate) (h : Good k es)
    (h1 : ∀ g ∈ new, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ i ∈ g.inputs, i < 2 * k + 2 + es.length) : Good k (es ++ new) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h.1 g hg
    · exact (h1 g hg).1
  · intro j hj i hi
    rcases Nat.lt_or_ge j es.length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact h.2 j hlt i hi
    · rw [List.getD_append_right _ _ _ _ hge] at hi
      have hlt : j - es.length < new.length := by rw [List.length_append] at hj; omega
      rw [List.getD_eq_getElem _ _ hlt] at hi
      have := (h1 _ (List.getElem_mem hlt)).2 i hi
      omega

theorem good_block (k : ℕ) (es : List Gate) (U : Finset (Fin k)) (mk : Finset (Fin k) → Gate)
    (h : Good k es)
    (hmk : ∀ τ, (((mk τ).op = GateOp.and ∨ (mk τ).op = GateOp.or) ∧ (mk τ).inputs.length ≤ 2) ∧
      ∀ i ∈ (mk τ).inputs, i < 2 * k + 2 + es.length) : Good k (es ++ (subs U).map mk) := by
  apply good_append k es _ h
  intro g hg
  obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hg
  exact hmk σ

theorem tab_elimMany {k : ℕ} (gs : List Gate) (U : Finset (Fin k)) (a : ℕ) (S : Finset (Fin k)) :
    Disjoint U S → ∀ (es : List Gate) (d : ℕ) (f : Finset (Fin k) → ℕ), Good k es →
      Tab gs es (U ∪ S) a d f →
      ∃ (new : List Gate) (f' : Finset (Fin k) → ℕ), Good k (es ++ new) ∧
        Tab gs (es ++ new) U a (S.card + d) f' ∧ new.length + 2 ^ U.card ≤ 2 ^ (U ∪ S).card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ es d f hG h
    exact ⟨[], f, by simpa using hG, by simpa using h, by simp⟩
  | insert v S' hv ih =>
    intro hdis es d f hG h
    have hvU : v ∉ U := (Finset.disjoint_insert_right.1 hdis).1
    have hdis' : Disjoint U S' := (Finset.disjoint_insert_right.1 hdis).2
    have hvUS : v ∉ U ∪ S' := by simp [hvU, hv]
    have e : U ∪ insert v S' = insert v (U ∪ S') := Finset.union_insert _ _ _
    rw [e] at h
    have h1 := tab_elim gs es (U ∪ S') v hvUS a d f h
    have hG1 := good_block k es (U ∪ S')
      (fun τ => (⟨GateOp.or, [f (τ.erase v), f (insert v τ)]⟩ : Gate)) hG (by
        intro τ
        refine ⟨⟨Or.inr rfl, le_refl _⟩, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact (h _).1
        · exact (h _).1)
    obtain ⟨new2, f', hG2, h2, hc⟩ := ih hdis' _ (1 + d) _ hG1 h1
    refine ⟨(subs (U ∪ S')).map (fun τ => (⟨GateOp.or, [f (τ.erase v), f (insert v τ)]⟩ : Gate)) ++ new2,
      f', by rw [← List.append_assoc]; exact hG2, ?_, ?_⟩
    · rw [← List.append_assoc]
      exact tab_mono _ _ _ _ _ _ (by rw [Finset.card_insert_of_notMem hv]; omega) _ h2
    · rw [e, Finset.card_insert_of_notMem hvUS, List.length_append, List.length_map, subs_length,
        pow_succ]
      omega

theorem tab_extMany {k : ℕ} (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (U : Finset (Fin k)) (a : ℕ) (S : Finset (Fin k)) :
    Disjoint U S → (∀ v ∈ S, v ∉ ((info k gs).getD a (∅, ∅)).1 ∧ v ∉ ((info k gs).getD a (∅, ∅)).2) →
      ∀ (es : List Gate) (d : ℕ) (f : Finset (Fin k) → ℕ), Good k es →
      Tab gs es U a d f →
      ∃ (new : List Gate) (f' : Finset (Fin k) → ℕ), Good k (es ++ new) ∧
        Tab gs (es ++ new) (U ∪ S) a (S.card + d) f' ∧
        new.length + 2 ^ (U.card + 1) ≤ 2 ^ ((U ∪ S).card + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ es d f hG h
    exact ⟨[], f, by simpa using hG, by simpa using h, by simp⟩
  | insert v S' hv ih =>
    intro hdis hS es d f hG h
    have hvU : v ∉ U := (Finset.disjoint_insert_right.1 hdis).1
    have hdis' : Disjoint U S' := (Finset.disjoint_insert_right.1 hdis).2
    have hvUS : v ∉ U ∪ S' := by simp [hvU, hv]
    have e : U ∪ insert v S' = insert v (U ∪ S') := Finset.union_insert _ _ _
    obtain ⟨new1, f1, hG1, h1, hc⟩ := ih hdis' (fun w hw => hS w (Finset.mem_insert_of_mem hw)) es d f hG h
    obtain ⟨hv1, hv2⟩ := hS v (Finset.mem_insert_self v S')
    have hlit : ∀ σ : Finset (Fin k), (if v ∈ σ then v.val else k + v.val) < 2 * k + 2 := by
      intro σ; split <;> omega
    have h2 := tab_ext gs (es ++ new1) hpos (U ∪ S') v a (S'.card + d) hv1 hv2 f1 h1
    have hG2 := good_block k (es ++ new1) (insert v (U ∪ S'))
      (fun τ => (⟨GateOp.and, [f1 τ, if v ∈ τ then v.val else k + v.val]⟩ : Gate)) hG1 (by
        intro τ
        refine ⟨⟨Or.inl rfl, le_refl _⟩, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact (h1 _).1
        · have := hlit τ; omega)
    refine ⟨new1 ++ (subs (insert v (U ∪ S'))).map
        (fun τ => (⟨GateOp.and, [f1 τ, if v ∈ τ then v.val else k + v.val]⟩ : Gate)),
      blockIdx (insert v (U ∪ S')) (es ++ new1), by rw [← List.append_assoc]; exact hG2, ?_, ?_⟩
    · rw [← List.append_assoc, e]
      exact tab_mono _ _ _ _ _ _ (by rw [Finset.card_insert_of_notMem hv]; omega) _ h2
    · rw [e, List.length_append, List.length_map, subs_length, Finset.card_insert_of_notMem hvUS,
        pow_succ]
      rw [pow_succ] at hc
      omega

theorem word_false {k : ℕ} (I O : Finset (Fin k)) : (word I O).getD (2 * k) false = false := by
  simp only [word, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_ofFn]
  have : 2 * k - k - k = 0 := by omega
  rw [this]; rfl

theorem word_true {k : ℕ} (I O : Finset (Fin k)) : (word I O).getD (2 * k + 1) false = true := by
  simp only [word, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_ofFn]
  have : 2 * k + 1 - k - k = 1 := by omega
  rw [this]; rfl

theorem tab_convert {k : ℕ} (gs : List Gate) (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (Ba Ut : Finset (Fin k)) (a : ℕ)
    (hleg : ∀ i ∈ Ut, (i ∈ ((info k gs).getD a (∅, ∅)).1 ∨ i ∈ ((info k gs).getD a (∅, ∅)).2) → i ∈ Ba)
    (es : List Gate) (d : ℕ) (f : Finset (Fin k) → ℕ) (hG : Good k es) (h : Tab gs es Ba a d f) :
    ∃ (new : List Gate) (f' : Finset (Fin k) → ℕ), Good k (es ++ new) ∧
      Tab gs (es ++ new) Ut a (Ba.card + Ut.card + d) f' ∧
      new.length ≤ 2 ^ Ba.card + 2 * 2 ^ Ut.card := by
  classical
  have e1 : (Ba ∩ Ut) ∪ (Ba \ Ut) = Ba := by
    ext i; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have d1 : Disjoint (Ba ∩ Ut) (Ba \ Ut) := by
    rw [Finset.disjoint_left]; intro i hi hi'; simp at hi hi'; tauto
  have h' : Tab gs es ((Ba ∩ Ut) ∪ (Ba \ Ut)) a d f := by rw [e1]; exact h
  obtain ⟨new1, f1, hG1, h1, c1⟩ := tab_elimMany gs (Ba ∩ Ut) a (Ba \ Ut) d1 es d f hG h'
  have e2 : (Ba ∩ Ut) ∪ (Ut \ Ba) = Ut := by
    ext i; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have d2 : Disjoint (Ba ∩ Ut) (Ut \ Ba) := by
    rw [Finset.disjoint_left]; intro i hi hi'; simp at hi hi'; tauto
  obtain ⟨new2, f2, hG2, h2, c2⟩ := tab_extMany gs hpos (Ba ∩ Ut) a (Ut \ Ba) d2 (by
    intro v hv
    simp only [Finset.mem_sdiff] at hv
    exact ⟨fun hh => hv.2 (hleg v hv.1 (Or.inl hh)), fun hh => hv.2 (hleg v hv.1 (Or.inr hh))⟩)
    (es ++ new1) _ f1 hG1 h1
  rw [e2] at h2 c2
  rw [e1] at c1
  refine ⟨new1 ++ new2, f2, by rw [← List.append_assoc]; exact hG2, ?_, ?_⟩
  · rw [← List.append_assoc]
    refine tab_mono _ _ _ _ _ _ ?_ _ h2
    have := Finset.card_le_card (Finset.sdiff_subset : Ba \ Ut ⊆ Ba)
    have := Finset.card_le_card (Finset.sdiff_subset : Ut \ Ba ⊆ Ut)
    omega
  · rw [List.length_append]
    simp only [pow_succ] at c2
    omega

theorem W_gate {k : ℕ} (A B' : List Gate) (g : Gate) (hrb : ∀ i ∈ g.inputs, i < 2 * k + 2 + A.length)
    (X : Finset (Fin k)) :
    W (A ++ [g] ++ B') X (2 * k + 2 + A.length) ↔
      g.op.eval (g.inputs.map fun i =>
        (wires (A ++ [g] ++ B') (word X (Finset.univ \ X))).getD i false) = true := by
  unfold W
  have := gate_val A B' g (word X (Finset.univ \ X)) (by rw [word_length]; exact hrb)
  rw [word_length] at this
  rw [this]

theorem gate_step {k : ℕ} (A B' : List Gate) (g : Gate)
    (hpos : ∀ g' ∈ A ++ [g] ++ B', g'.op = GateOp.and ∨ g'.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hrb : ∀ i ∈ g.inputs, i < 2 * k + 2 + A.length)
    (Bg : ℕ → Finset (Fin k)) (U : Finset (Fin k)) (w : ℕ)
    (hUw : U.card ≤ w) (hBw : ∀ i ∈ g.inputs, (Bg i).card ≤ w)
    (hleg : ∀ i ∈ g.inputs, ∀ v ∈ U, (v ∈ ((info k (A ++ [g] ++ B')).getD i (∅, ∅)).1 ∨
      v ∈ ((info k (A ++ [g] ++ B')).getD i (∅, ∅)).2) → v ∈ Bg i)
    (hUv : ∀ v ∈ U, v ∈ ((info k (A ++ [g] ++ B')).getD (2 * k + 2 + A.length) (∅, ∅)).1 ∨
      v ∈ ((info k (A ++ [g] ++ B')).getD (2 * k + 2 + A.length) (∅, ∅)).2)
    (hcross : g.op = GateOp.and → ∀ a b, g.inputs = [a, b] → ∀ v,
      (v ∈ ((info k (A ++ [g] ++ B')).getD a (∅, ∅)).1 ∧ v ∈ ((info k (A ++ [g] ++ B')).getD b (∅, ∅)).2) ∨
      (v ∈ ((info k (A ++ [g] ++ B')).getD a (∅, ∅)).2 ∧ v ∈ ((info k (A ++ [g] ++ B')).getD b (∅, ∅)).1) →
      v ∈ U)
    (es : List Gate) (d : ℕ) (S : ℕ → Finset (Fin k) → ℕ) (hG : Good k es)
    (hS : ∀ i ∈ g.inputs, Tab (A ++ [g] ++ B') es (Bg i) i d (S i)) :
    ∃ (new : List Gate) (f' : Finset (Fin k) → ℕ), Good k (es ++ new) ∧
      Tab (A ++ [g] ++ B') (es ++ new) U (2 * k + 2 + A.length) (2 * w + 1 + d) f' ∧
      new.length ≤ 7 * 2 ^ w := by
  classical
  have hWg := W_gate A B' g hrb
  have hpw : ∀ c : ℕ, c ≤ w → 2 ^ c ≤ 2 ^ w := fun c hc => Nat.pow_le_pow_right (by norm_num) hc
  have hw1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  match hin : g.inputs, hlen with
  | [], _ =>
    have hU0 : U = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      have := hUv v hv
      rw [info_gate] at this
      simp [infoF, hin] at this
    subst hU0
    rw [hin] at hWg
    rcases hpos g (by simp) with ho | ho
    · refine ⟨[], fun _ => 2 * k + 1, by simpa using hG, ?_, by simp⟩
      intro τ
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only
      · rw [List.length_append]; omega
      · rw [dep_input _ _ _ (by omega)]; exact Nat.zero_le _
      intro I O hIO
      rw [wires_input _ _ _ (by rw [word_length]; omega), word_true]
      have hI : ∀ i : Fin k, i ∈ I ∨ i ∈ O := fun i => by
        have : i ∈ I ∪ O := by rw [hIO]; exact Finset.mem_univ i
        simpa using this
      simp only [true_iff]
      exact ⟨I, ⟨fun i hi => hi, fun i hi => (hI i).resolve_left hi⟩, by simp,
        (hWg I).2 (by simp [ho, GateOp.eval])⟩
    · refine ⟨[], fun _ => 2 * k, by simpa using hG, ?_, by simp⟩
      intro τ
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only
      · rw [List.length_append]; omega
      · rw [dep_input _ _ _ (by omega)]; exact Nat.zero_le _
      intro I O hIO
      rw [wires_input _ _ _ (by rw [word_length]; omega), word_false]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨X, _, _, hw⟩
      have := (hWg X).1 hw
      simp [ho, GateOp.eval] at this
  | [a], _ =>
    have ha : a ∈ g.inputs := by simp [hin]
    obtain ⟨new1, f1, hG1, h1, c1⟩ := tab_convert (A ++ [g] ++ B') hpos (Bg a) U a (hleg a ha) es d
      (S a) hG (hS a ha)
    refine ⟨new1, f1, hG1, ?_, ?_⟩
    · intro τ
      obtain ⟨t1, t2, t3⟩ := h1 τ
      refine ⟨t1, by have := hBw a ha; omega, ?_⟩
      intro I O hIO
      rw [t3 I O hIO]
      have hWa : ∀ X : Finset (Fin k), W (A ++ [g] ++ B') X (2 * k + 2 + A.length) ↔
          W (A ++ [g] ++ B') X a := by
        intro X
        rw [hWg X, hin]
        rcases hpos g (by simp) with ho | ho <;> simp [ho, GateOp.eval, W]
      unfold Sem
      simp only [hWa]
    · have := hpw _ (hBw a ha); have := hpw _ hUw; omega
  | [a, b], _ =>
    have ha : a ∈ g.inputs := by simp [hin]
    have hb : b ∈ g.inputs := by simp [hin]
    obtain ⟨new1, f1, hG1, h1, c1⟩ := tab_convert (A ++ [g] ++ B') hpos (Bg a) U a (hleg a ha) es d
      (S a) hG (hS a ha)
    obtain ⟨new2, f2, hG2, h2, c2⟩ := tab_convert (A ++ [g] ++ B') hpos (Bg b) U b (hleg b hb)
      (es ++ new1) d (S b) hG1 (tab_append _ _ _ _ _ _ _ (hS b hb))
    have h1' := tab_append _ _ new2 _ _ _ _ h1
    have hmk : ∀ τ : Finset (Fin k), ∀ i ∈ ([f1 τ, f2 τ] : List ℕ),
        i < 2 * k + 2 + (es ++ new1 ++ new2).length := by
      intro τ i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact (h1' _).1
      · exact (h2 _).1
    have hG3 := good_block k (es ++ new1 ++ new2) U (fun τ => (⟨g.op, [f1 τ, f2 τ]⟩ : Gate)) hG2
      (fun τ => ⟨⟨hpos g (by simp), le_refl _⟩, hmk τ⟩)
    refine ⟨new1 ++ new2 ++ (subs U).map (fun τ => (⟨g.op, [f1 τ, f2 τ]⟩ : Gate)), blockIdx U (es ++ new1 ++ new2),
      by simpa [List.append_assoc] using hG3, ?_, ?_⟩
    · have e : es ++ (new1 ++ new2 ++ (subs U).map (fun τ => (⟨g.op, [f1 τ, f2 τ]⟩ : Gate))) =
          es ++ new1 ++ new2 ++ (subs U).map (fun τ => (⟨g.op, [f1 τ, f2 τ]⟩ : Gate)) := by
        simp [List.append_assoc]
      rw [e]
      intro τ
      obtain ⟨b1, b2, b3⟩ := block_spec (es ++ new1 ++ new2) U
        (fun τ => (⟨g.op, [f1 τ, f2 τ]⟩ : Gate)) hmk τ
      have hda := hBw a ha
      have hdb := hBw b hb
      refine ⟨b1, (b3 (2 * w + d) (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have := (h1' (τ ∩ U)).2.1; omega
        · have := (h2 (τ ∩ U)).2.1; omega)).trans (by omega), ?_⟩
      intro I O hIO
      rw [b2 I O, ← sem_inter]
      have s1 := (h1' (τ ∩ U)).2.2 I O hIO
      have s2 := (h2 (τ ∩ U)).2.2 I O hIO
      rcases hpos g (by simp) with ho | ho
      · have key := and_comb k (A ++ [g] ++ B') hpos a b I O (τ ∩ U) U (hcross ho a b hin)
        rw [← s1, ← s2] at key
        have hWab : ∀ X : Finset (Fin k), W (A ++ [g] ++ B') X (2 * k + 2 + A.length) ↔
            (W (A ++ [g] ++ B') X a ∧ W (A ++ [g] ++ B') X b) := by
          intro X
          rw [hWg X, hin]
          simp [ho, GateOp.eval, W]
        unfold Sem
        simp only [hWab]
        rw [key]
        simp [ho, GateOp.eval]
      · have key := or_comb k (A ++ [g] ++ B') a b I O (τ ∩ U) U
        rw [← s1, ← s2] at key
        have hWab : ∀ X : Finset (Fin k), W (A ++ [g] ++ B') X (2 * k + 2 + A.length) ↔
            (W (A ++ [g] ++ B') X a ∨ W (A ++ [g] ++ B') X b) := by
          intro X
          rw [hWg X, hin]
          simp [ho, GateOp.eval, W]
        unfold Sem
        simp only [hWab]
        rw [key]
        simp [ho, GateOp.eval]
    · simp only [List.length_append, List.length_map, subs_length]
      have := hpw _ (hBw a ha); have := hpw _ (hBw b hb); have := hpw _ hUw; omega
  | _ :: _ :: _ :: _, hl => exact absurd hl (by simp)

theorem info_input (k : ℕ) (gs : List Gate) (j : ℕ) (hj : j < 2 * k + 2) :
    (info k gs).getD j (∅, ∅) = (info0 k).getD j (∅, ∅) := by
  have := info_prefix k [] gs j (by simpa using hj)
  rw [List.nil_append] at this
  rw [this]; rfl

theorem input_tab {k : ℕ} (gs : List Gate) (U : Finset (Fin k)) (j : ℕ) (hj : j < 2 * k + 2)
    (hU : ∀ v ∈ U, v ∈ ((info k gs).getD j (∅, ∅)).1 ∨ v ∈ ((info k gs).getD j (∅, ∅)).2) :
    ∃ f : Finset (Fin k) → ℕ, Tab gs [] U j 0 f := by
  classical
  have hWj : ∀ X : Finset (Fin k), W gs X j ↔ (word X (Finset.univ \ X)).getD j false = true := by
    intro X; unfold W; rw [wires_input _ _ _ (by rw [word_length]; exact hj)]
  have hmemIO : ∀ I O : Finset (Fin k), I ∪ O = Finset.univ → ∀ i : Fin k, i ∈ I ∨ i ∈ O := by
    intro I O hIO i
    have : i ∈ I ∪ O := by rw [hIO]; exact Finset.mem_univ i
    simpa using this
  rcases Nat.lt_or_ge j k with h | h
  · have e := fun (A B : Finset (Fin k)) => word_x A B ⟨j, h⟩
    simp only at e
    have hinfo : (info k gs).getD j (∅, ∅) = ({⟨j, h⟩}, ∅) := by
      rw [info_input k gs j hj]; exact info0_x k ⟨j, h⟩
    have hU' : ∀ v ∈ U, v = ⟨j, h⟩ := by
      intro v hv; have := hU v hv; rw [hinfo] at this; simpa using this
    refine ⟨fun τ => if (⟨j, h⟩ : Fin k) ∈ U ∧ (⟨j, h⟩ : Fin k) ∉ τ then 2 * k else j, ?_⟩
    intro τ
    by_cases hc : (⟨j, h⟩ : Fin k) ∈ U ∧ (⟨j, h⟩ : Fin k) ∉ τ
    · simp only [if_pos hc]
      refine ⟨by simp, by rw [dep_input _ _ _ (by omega)], ?_⟩
      intro I O hIO
      rw [wires_input _ _ _ (by rw [word_length]; omega), word_false]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨X, _, hag, hw⟩
      rw [hWj, e] at hw
      exact hc.2 ((hag _ hc.1).1 hw)
    · simp only [if_neg hc]
      refine ⟨by simpa using hj, by rw [dep_input _ _ _ hj], ?_⟩
      intro I O hIO
      rw [wires_input _ _ _ (by rw [word_length]; omega), e]
      constructor
      · intro hI
        refine ⟨I, ⟨fun i hi => hi, fun i hi => (hmemIO I O hIO i).resolve_left hi⟩, ?_, ?_⟩
        · intro v hv
          have hvj := hU' v hv
          subst hvj
          have : (⟨j, h⟩ : Fin k) ∈ τ := by by_contra hn; exact hc ⟨hv, hn⟩
          simp [hI, this]
        · rw [hWj, e]; exact hI
      · rintro ⟨X, ⟨f1, _⟩, _, hw⟩
        rw [hWj, e] at hw
        exact f1 _ hw
  · rcases Nat.lt_or_ge j (2 * k) with h2 | h2
    · have hjk : j - k < k := by omega
      have e := fun (A B : Finset (Fin k)) => word_z A B ⟨j - k, hjk⟩
      simp only at e
      rw [show k + (j - k) = j by omega] at e
      have hinfo : (info k gs).getD j (∅, ∅) = (∅, {⟨j - k, hjk⟩}) := by
        rw [info_input k gs j hj]
        have := info0_z k ⟨j - k, hjk⟩
        simp only at this
        rw [show k + (j - k) = j by omega] at this
        exact this
      have hU' : ∀ v ∈ U, v = ⟨j - k, hjk⟩ := by
        intro v hv; have := hU v hv; rw [hinfo] at this; simpa using this
      refine ⟨fun τ => if (⟨j - k, hjk⟩ : Fin k) ∈ U ∧ (⟨j - k, hjk⟩ : Fin k) ∈ τ then 2 * k else j, ?_⟩
      intro τ
      by_cases hc : (⟨j - k, hjk⟩ : Fin k) ∈ U ∧ (⟨j - k, hjk⟩ : Fin k) ∈ τ
      · simp only [if_pos hc]
        refine ⟨by simp, by rw [dep_input _ _ _ (by omega)], ?_⟩
        intro I O hIO
        rw [wires_input _ _ _ (by rw [word_length]; omega), word_false]
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨X, _, hag, hw⟩
        rw [hWj, e] at hw
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hw
        exact hw ((hag _ hc.1).2 hc.2)
      · simp only [if_neg hc]
        refine ⟨by simpa using hj, by rw [dep_input _ _ _ hj], ?_⟩
        intro I O hIO
        rw [wires_input _ _ _ (by rw [word_length]; omega), e]
        constructor
        · intro hO
          refine ⟨Finset.univ \ O, ⟨fun i hi => (hmemIO I O hIO i).resolve_right (by simpa using hi),
            fun i hi => by simpa using hi⟩, ?_, ?_⟩
          · intro v hv
            have hvj := hU' v hv
            subst hvj
            have : (⟨j - k, hjk⟩ : Fin k) ∉ τ := fun hn => hc ⟨hv, hn⟩
            simp [hO, this]
          · rw [hWj, e]; simpa using hO
        · rintro ⟨X, ⟨_, f2⟩, _, hw⟩
          rw [hWj, e] at hw
          exact f2 _ (by simpa using hw)
    · have hinfo : (info k gs).getD j (∅, ∅) = (∅, ∅) := by
        rw [info_input k gs j hj]; exact info0_c k j h2
      have hU0 : U = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv; have := hU v hv; rw [hinfo] at this; simp at this
      subst hU0
      refine ⟨fun _ => j, ?_⟩
      intro τ
      refine ⟨by simpa using hj, by rw [dep_input _ _ _ hj], ?_⟩
      intro I O hIO
      rw [wires_input _ _ _ (by rw [word_length]; omega), input_sem k gs I O hIO j hj]
      simp [Sem]

theorem input_tap {k : ℕ} (gs : List Gate) (j : ℕ) (hj : j < 2 * k + 2) :
    Tab gs [] (∅ : Finset (Fin k)) j 0 (fun _ => j) := by
  intro τ
  refine ⟨by simpa using hj, by rw [dep_input _ _ _ hj], ?_⟩
  intro I O hIO
  rw [wires_input _ _ _ (by rw [word_length]; omega), input_sem k gs I O hIO j hj]
  simp [Sem]

theorem foldmax_ge (ts : List ℕ) (l : List ℕ) (m : ℕ) :
    m ≤ l.foldl (fun m j => max m (ts.getD j 0)) m ∧
      ∀ i ∈ l, ts.getD i 0 ≤ l.foldl (fun m j => max m (ts.getD j 0)) m := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max m (ts.getD a 0))
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    rintro i (rfl | hi)
    · exact le_trans (le_max_right _ _) h1
    · exact h2 i hi

theorem dep_gate_ge (n : ℕ) (A B : List Gate) (g : Gate) (i : ℕ) (hi : i ∈ g.inputs)
    (hlt : i < n + A.length) :
    (dep n (A ++ [g] ++ B)).getD i 0 + 1 ≤ (dep n (A ++ [g] ++ B)).getD (n + A.length) 0 := by
  rw [dep_gate, List.append_assoc, dep_prefix n A ([g] ++ B) i hlt]
  unfold depF
  have := (foldmax_ge (dep n A) g.inputs 0).2 i hi
  omega

theorem main_aux {k : ℕ} (w : ℕ) (gs : List Gate)
    (hpos : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hrb : ∀ t (ht : t < gs.length), ∀ i ∈ gs[t].inputs, i < 2 * k + 2 + t)
    (Bh : ℕ → Finset (Fin k)) (cr : ℕ → Finset (Fin k))
    (hsub : ∀ j, j < 2 * k + 2 + gs.length → ∀ v ∈ Bh j,
      v ∈ ((info k gs).getD j (∅, ∅)).1 ∨ v ∈ ((info k gs).getD j (∅, ∅)).2)
    (hcrv : ∀ t, t < gs.length → ∀ v ∈ cr t,
      v ∈ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).1 ∨ v ∈ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).2)
    (hcr : ∀ t (ht : t < gs.length), gs[t].op = GateOp.and → ∀ a b, gs[t].inputs = [a, b] → ∀ v,
      (v ∈ ((info k gs).getD a (∅, ∅)).1 ∧ v ∈ ((info k gs).getD b (∅, ∅)).2) ∨
      (v ∈ ((info k gs).getD a (∅, ∅)).2 ∧ v ∈ ((info k gs).getD b (∅, ∅)).1) → v ∈ cr t)
    (hleg : ∀ t (ht : t < gs.length), ∀ j ∈ gs[t].inputs, ∀ v ∈ Bh (2 * k + 2 + t) ∪ cr t,
      (v ∈ ((info k gs).getD j (∅, ∅)).1 ∨ v ∈ ((info k gs).getD j (∅, ∅)).2) → v ∈ Bh j)
    (hb1 : ∀ j, j < 2 * k + 2 → (Bh j).card ≤ w)
    (hb2 : ∀ t, t < gs.length → (Bh (2 * k + 2 + t) ∪ cr t).card ≤ w) :
    ∀ m, m ≤ gs.length → ∃ (es : List Gate) (S T : ℕ → Finset (Fin k) → ℕ), Good k es ∧
      es.length ≤ 13 * 2 ^ w * m ∧ ∀ j, j < 2 * k + 2 + m →
        Tab gs es (Bh j) j ((4 * w + 1) * (dep (2 * k + 2) gs).getD j 0) (S j) ∧
        Tab gs es ∅ j ((4 * w + 1) * (dep (2 * k + 2) gs).getD j 0 + 2 * w) (T j) := by
  classical
  have hBcard : ∀ i, i < 2 * k + 2 + gs.length → (Bh i).card ≤ w := by
    intro i hi
    rcases Nat.lt_or_ge i (2 * k + 2) with h | h
    · exact hb1 i h
    · have := hb2 (i - (2 * k + 2)) (by omega)
      rw [show 2 * k + 2 + (i - (2 * k + 2)) = i by omega] at this
      exact le_trans (Finset.card_le_card Finset.subset_union_left) this
  have hpw : ∀ c : ℕ, c ≤ w → 2 ^ c ≤ 2 ^ w := fun c hc => Nat.pow_le_pow_right (by norm_num) hc
  intro m
  induction m with
  | zero =>
    intro _
    have hex : ∀ j, j < 2 * k + 2 → ∃ f, Tab gs [] (Bh j) j 0 f :=
      fun j hj => input_tab gs (Bh j) j hj (hsub j (by omega))
    choose! S hS using hex
    refine ⟨[], S, fun j _ => j, ⟨by simp, by simp⟩, by simp, ?_⟩
    intro j hj
    exact ⟨tab_mono _ _ _ _ _ _ (Nat.zero_le _) _ (hS j (by omega)),
      tab_mono _ _ _ _ _ _ (Nat.zero_le _) _ (input_tap gs j (by omega))⟩
  | succ m ih =>
    intro hm
    obtain ⟨es, S, T, hG, hsz, hT⟩ := ih (by omega)
    have hmlt : m < gs.length := by omega
    have hsplit : gs = gs.take m ++ [gs[m]] ++ gs.drop (m + 1) := by simp
    have hAl : (gs.take m).length = m := by rw [List.length_take]; omega
    have hdep : ∀ i ∈ gs[m].inputs,
        (dep (2 * k + 2) gs).getD i 0 + 1 ≤ (dep (2 * k + 2) gs).getD (2 * k + 2 + m) 0 := by
      intro i hi
      have := dep_gate_ge (2 * k + 2) (gs.take m) (gs.drop (m + 1)) gs[m] i hi
        (by rw [hAl]; exact hrb m hmlt i hi)
      rw [← hsplit, hAl] at this
      exact this
    have hd1 : 1 ≤ (dep (2 * k + 2) gs).getD (2 * k + 2 + m) 0 := by
      have := dep_gate (2 * k + 2) (gs.take m) (gs.drop (m + 1)) gs[m]
      rw [← hsplit, hAl] at this
      rw [this]; unfold depF; omega
    have hmul : (4 * w + 1) * ((dep (2 * k + 2) gs).getD (2 * k + 2 + m) 0 - 1) + (4 * w + 1) =
        (4 * w + 1) * (dep (2 * k + 2) gs).getD (2 * k + 2 + m) 0 := by
      rw [← Nat.mul_succ]; congr 1; omega
    have gst := gate_step (gs.take m) (gs.drop (m + 1)) gs[m] (by rw [← hsplit]; exact hpos)
      (hlen _ (List.getElem_mem hmlt)) (by rw [hAl]; exact hrb m hmlt) Bh
      (Bh (2 * k + 2 + m) ∪ cr m) w (hb2 m hmlt)
      (fun i hi => hBcard i (by have := hrb m hmlt i hi; omega))
      (by rw [← hsplit]; exact hleg m hmlt)
      (by
        rw [← hsplit, hAl]
        intro v hv
        rcases Finset.mem_union.1 hv with h | h
        · exact hsub _ (by omega) v h
        · exact hcrv m hmlt v h)
      (by
        rw [← hsplit]
        intro ho a b hab v hv
        exact Finset.mem_union_right _ (hcr m hmlt ho a b hab v hv))
      es ((4 * w + 1) * ((dep (2 * k + 2) gs).getD (2 * k + 2 + m) 0 - 1)) S hG
      (by
        rw [← hsplit]
        intro i hi
        exact tab_mono _ _ _ _ _ _ (Nat.mul_le_mul_left _ (by have := hdep i hi; omega)) _
          (hT i (hrb m hmlt i hi)).1)
    rw [← hsplit, hAl] at gst
    obtain ⟨new1, f1, hG1, h1, c1⟩ := gst
    have eU : Bh (2 * k + 2 + m) ∪ (cr m \ Bh (2 * k + 2 + m)) = Bh (2 * k + 2 + m) ∪ cr m :=
      Finset.union_sdiff_self_eq_union
    have hcard : (Bh (2 * k + 2 + m)).card + (cr m \ Bh (2 * k + 2 + m)).card ≤ w := by
      have := Finset.card_union_of_disjoint
        (Finset.disjoint_sdiff : Disjoint (Bh (2 * k + 2 + m)) (cr m \ Bh (2 * k + 2 + m)))
      rw [eU] at this
      have := hb2 m hmlt
      omega
    obtain ⟨new2, f2, hG2, h2, c2⟩ := tab_elimMany gs (Bh (2 * k + 2 + m)) (2 * k + 2 + m)
      (cr m \ Bh (2 * k + 2 + m)) Finset.disjoint_sdiff (es ++ new1) _ f1 hG1 (by rw [eU]; exact h1)
    rw [eU] at c2
    obtain ⟨new3, f3, hG3, h3, c3⟩ := tab_elimMany gs ∅ (2 * k + 2 + m)
      (Bh (2 * k + 2 + m)) (Finset.disjoint_empty_left _) (es ++ new1 ++ new2) _ f2 hG2
      (by rw [Finset.empty_union]; exact h2)
    rw [Finset.empty_union] at c3
    refine ⟨es ++ new1 ++ new2 ++ new3, fun j => if j = 2 * k + 2 + m then f2 else S j,
      fun j => if j = 2 * k + 2 + m then f3 else T j, hG3, ?_, ?_⟩
    · simp only [List.length_append]
      have p1 := hpw _ (hb2 m hmlt)
      have p2 := hpw _ (hBcard (2 * k + 2 + m) (by omega))
      simp only [Finset.card_empty, pow_zero] at c3
      rw [Nat.mul_succ]
      omega
    · intro j hj
      by_cases hjm : j = 2 * k + 2 + m
      · subst hjm
        simp only [if_true]
        refine ⟨tab_append _ _ _ _ _ _ _ (tab_mono _ _ _ _ _ _ (by omega) _ h2),
          tab_mono _ _ _ _ _ _ (by omega) _ h3⟩
      · simp only [if_neg hjm]
        obtain ⟨a1, a2⟩ := hT j (by omega)
        exact ⟨tab_append _ _ _ _ _ _ _ (tab_append _ _ _ _ _ _ _ (tab_append _ _ _ _ _ _ _ a1)),
          tab_append _ _ _ _ _ _ _ (tab_append _ _ _ _ _ _ _ (tab_append _ _ _ _ _ _ _ a2))⟩

theorem info_sub_full {k : ℕ} (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hrbt : ∀ i ∈ gs[t].inputs, i < 2 * k + 2 + t) (i : ℕ) (hi : i ∈ gs[t].inputs) :
    ((info k gs).getD i (∅, ∅)).1 ⊆ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).1 ∧
      ((info k gs).getD i (∅, ∅)).2 ⊆ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).2 := by
  have hsplit : gs = gs.take t ++ [gs[t]] ++ gs.drop (t + 1) := by simp
  have hAl : (gs.take t).length = t := by rw [List.length_take]; omega
  have := info_gate_sub k (gs.take t) (gs.drop (t + 1)) gs[t] i hi (by rw [hAl]; exact hrbt i hi)
  rw [← hsplit, hAl] at this
  exact this

noncomputable def crossF (k : ℕ) (gs : List Gate) (t : ℕ) : Finset (Fin k) :=
  let g := gs.getD t ⟨GateOp.or, []⟩
  let a := (g.inputs.head?.map (fun j => (info k gs).getD j ((∅, ∅) : Finset (Fin k) × Finset (Fin k)))).getD (∅, ∅)
  let b := (g.inputs[1]?.map (fun j => (info k gs).getD j ((∅, ∅) : Finset (Fin k) × Finset (Fin k)))).getD (∅, ∅)
  @ite _ (g.op = GateOp.and) (Classical.propDecidable _) ((a.1 ∩ b.2) ∪ (a.2 ∩ b.1)) ∅

theorem crossF_mem {k : ℕ} (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (ho : gs[t].op = GateOp.and) (a b : ℕ) (hab : gs[t].inputs = [a, b]) (v : Fin k)
    (hv : (v ∈ ((info k gs).getD a (∅, ∅)).1 ∧ v ∈ ((info k gs).getD b (∅, ∅)).2) ∨
      (v ∈ ((info k gs).getD a (∅, ∅)).2 ∧ v ∈ ((info k gs).getD b (∅, ∅)).1)) :
    v ∈ crossF k gs t := by
  unfold crossF
  rw [List.getD_eq_getElem _ _ ht]
  dsimp only
  rw [if_pos ho, hab]
  simpa [Finset.mem_union, Finset.mem_inter] using hv

theorem crossF_sub {k : ℕ} (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hrbt : ∀ i ∈ gs[t].inputs, i < 2 * k + 2 + t) (v : Fin k) (hv : v ∈ crossF k gs t) :
    v ∈ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).1 ∨
      v ∈ ((info k gs).getD (2 * k + 2 + t) (∅, ∅)).2 := by
  unfold crossF at hv
  rw [List.getD_eq_getElem _ _ ht] at hv
  dsimp only at hv
  by_cases ho : gs[t].op = GateOp.and
  · rw [if_pos ho] at hv
    match hin : gs[t].inputs with
    | [] => rw [hin] at hv; simp at hv
    | a :: l =>
      have ha : a ∈ gs[t].inputs := by rw [hin]; simp
      obtain ⟨s1, s2⟩ := info_sub_full gs t ht hrbt a ha
      rw [hin] at hv
      simp only [List.head?_cons, Option.map_some, Option.getD_some, Finset.mem_union,
        Finset.mem_inter] at hv
      rcases hv with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (s1 h)
      · exact Or.inr (s2 h)
  · rw [if_neg ho] at hv; simp at hv

theorem mem_union_cl {k : ℕ} {s t : Finset (Fin k)} {v : Fin k} (h : v ∈ s ∪ t) : v ∈ s ∨ v ∈ t :=
  Finset.mem_union.1 h

theorem mem_inter_union_cl {k : ℕ} {A s t : Finset (Fin k)} {v : Fin k} (h : v ∈ A)
    (h' : v ∈ s ∨ v ∈ t) : v ∈ A ∩ (s ∪ t) :=
  Finset.mem_inter.2 ⟨h, Finset.mem_union.2 h'⟩

end

end PEqualNP.Outside.L_lib_1480_aux

theorem PEqualNP.Outside.L_lib_1480 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let word := fun {k : Nat} (ones zeros : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ ones)) ++
  List.ofFn (fun j : Fin k => decide (j ∈ zeros)) ++ [false,true]
let fits := fun {k : Nat} (X I O : Finset (Fin k)) => X ⊆ I ∧ Finset.univ \ X ⊆ O
let wireInfo := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
  let xs := List.ofFn (fun j : Fin k => (({j},∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅,{j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z,Z]
  D.gates.foldl (fun (ts : List (Finset (Fin k) × Finset (Fin k))) g =>
    ts ++ [g.inputs.foldl (fun v t => let a := ts.getD t Z
                                      (v.1 ∪ a.1,v.2 ∪ a.2)) Z]) xs
let gateAt := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (t : Nat) => D.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
let depths := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  D.gates.foldl (fun (ts : List Nat) g =>
    ts ++ [1+g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0]) (List.replicate (h+2) 0)
∀ (k budget : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (held : Nat → Finset (Fin k)), pos (2*k) D →
let src := 2*k+2
let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
let info := wireInfo k D
let vars := fun (j : Nat) => let s := info.getD j Z
                             s.1 ∪ s.2
let cross := fun (t : Nat) =>
  let g := gateAt D t
  let a := (g.inputs.head?.map (fun j => info.getD j Z)).getD Z
  let b := (g.inputs[1]?.map (fun j => info.getD j Z)).getD Z
  if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) else ∅
let legal := fun (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src+D.size → B j ⊆ vars j) ∧
  ∀ t, t<D.size → ∀ j ∈ (gateAt D t).inputs, (B (src+t) ∪ cross t) ∩ vars j ⊆ B j
let bounded := fun (w : Nat) (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src → (B j).card ≤ w) ∧ ∀ t, t<D.size → (B (src+t) ∪ cross t).card ≤ w
legal held → bounded budget held →
∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (tap : Nat → Nat), pos (2*k) E ∧ E.size ≤ 13 * 2^budget * D.size ∧
  tap D.output=E.output ∧ ∀ j, j<src+D.size →
    tap j < src+E.size ∧
    (depths (2*k) E).getD (tap j) 0 ≤ (4*budget+1)*((depths (2*k) D).getD j 0)+2*budget ∧
    ∀ I O : Finset (Fin k), I ∪ O=Finset.univ →
      ((E.wires (word I O)).getD (tap j) false=true ↔
        ∃ X : Finset (Fin k), fits X I O ∧
          (D.wires (word X (Finset.univ \ X))).getD j false=true)) := by
  intro valid pos word fits wireInfo gateAt depths k budget D held hD src Z info vars cross legal
    bounded hlegal hbounded
  obtain ⟨⟨hF, hRB, hout⟩, hnc⟩ := hD
  obtain ⟨hl1, hl2⟩ := hlegal
  obtain ⟨hbd1, hbd2⟩ := hbounded
  have hposg : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have h1 := (hF g hg).1
    have h2 : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro h
      unfold PEqualNP.NotBracket.notCount at hnc
      have hnc' := List.length_eq_zero_iff.1 hnc
      have := List.filter_eq_nil_iff.1 hnc' g hg
      simp [h] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    tauto
  have hlen : ∀ g ∈ D.gates, g.inputs.length ≤ 2 := fun g hg => (hF g hg).2
  have hrb : ∀ t (ht : t < D.gates.length), ∀ i ∈ D.gates[t].inputs, i < 2 * k + 2 + t := by
    intro t ht i hi
    exact hRB t ht i (by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ ht]; exact hi)
  obtain ⟨es, S, T, hG, hsz, hT⟩ := PEqualNP.Outside.L_lib_1480_aux.main_aux budget D.gates hposg hlen hrb
    held (PEqualNP.Outside.L_lib_1480_aux.crossF k D.gates)
    (fun j hj v hv => PEqualNP.Outside.L_lib_1480_aux.mem_union_cl (hl1 j hj hv))
    (fun t ht v hv => PEqualNP.Outside.L_lib_1480_aux.crossF_sub D.gates t ht (hrb t ht) v hv)
    (fun t ht ho a b hab v hv => PEqualNP.Outside.L_lib_1480_aux.crossF_mem D.gates t ht ho a b hab v hv)
    (fun t ht j hj v hv hvj => hl2 t ht j (by
        show j ∈ (D.gates.getD t _).inputs
        rw [List.getD_eq_getElem _ _ ht]; exact hj)
      (PEqualNP.Outside.L_lib_1480_aux.mem_inter_union_cl hv hvj))
    hbd1 hbd2 D.gates.length le_rfl
  refine ⟨⟨es, T D.output ∅⟩, fun j => T j ∅, ⟨⟨?_, hG.2, ((hT D.output hout).2 ∅).1⟩, ?_⟩, hsz, rfl, ?_⟩
  · intro g hg
    refine ⟨?_, (hG.1 g hg).2⟩
    rcases (hG.1 g hg).1 with h | h <;> simp [h]
  · unfold PEqualNP.NotBracket.notCount
    refine List.length_eq_zero_iff.2 (List.filter_eq_nil_iff.2 ?_)
    intro g hg
    rcases (hG.1 g hg).1 with h | h <;> simp [h]
  · intro j hj
    obtain ⟨t1, t2, t3⟩ := (hT j hj).2 ∅
    refine ⟨t1, t2, fun I O hIO => ?_⟩
    refine (t3 I O hIO).trans ?_
    constructor
    · rintro ⟨X, hf, _, hw⟩
      exact ⟨X, (PEqualNP.Outside.L_lib_1480_aux.fits_iff X I O).1 hf, hw⟩
    · rintro ⟨X, hf, hw⟩
      exact ⟨X, (PEqualNP.Outside.L_lib_1480_aux.fits_iff X I O).2 hf, by simp, hw⟩
