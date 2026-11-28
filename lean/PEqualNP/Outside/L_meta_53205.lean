import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53205
open PEqualNP.CircuitLowerBounds
section Circ
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Wr (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : Wr (gs ++ [g]) x = stp (Wr gs x) g := by
  simp [Wr, List.foldl_append]
theorem W_len (gs : List Gate) (x : List Bool) : (Wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Wr]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega
theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]
theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (Wr gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [Wr]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih
theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (Wr (gs ++ [g]) x).getD i false = (Wr gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]
theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (Wr gs x).getD i false = (Wr (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]
theorem eval_mono (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hle : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases h with h | h <;> rw [h] at hv ⊢
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at hv ⊢
    intro i hi; exact hle i hi (hv i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨v, ⟨i, hi, rfl⟩, hv⟩ := hv
    exact ⟨true, ⟨i, hi, hle i hi hv⟩, rfl⟩
theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (X Y : List Bool)
    (hl : X.length = Y.length)
    (hle : ∀ i, X.getD i false = true → Y.getD i false = true) :
    ∀ i, (Wr gs X).getD i false = true → (Wr gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [Wr] using hle
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro i
    rw [W_snoc, W_snoc]
    unfold stp
    have e1 : (Wr gs X).length = X.length + gs.length := W_len _ _
    have e2 : (Wr gs Y).length = X.length + gs.length := by rw [W_len, hl]
    rcases lt_trichotomy i (X.length + gs.length) with h | h | h
    · rw [getD_app_l _ _ _ (by omega), getD_app_l _ _ _ (by omega)]; exact ih' i
    · subst h
      have a1 := getD_app_m (Wr gs X) (g.op.eval (g.inputs.map fun i => (Wr gs X).getD i false))
      have a2 := getD_app_m (Wr gs Y) (g.op.eval (g.inputs.map fun i => (Wr gs Y).getD i false))
      rw [e1] at a1
      rw [e2] at a2
      rw [a1, a2]
      exact eval_mono g (hm g (by simp)) _ _ (fun k _ => ih' k)
    · rw [getD_big _ _ (by simp [e1]; omega)]
      intro hf
      exact absurd hf (by decide)
def Good (N : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length),
  ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) ∧ (gs[j]).inputs.length ≤ 2 ∧
    ∀ i ∈ (gs[j]).inputs, i < N + j
theorem good_nil (N : ℕ) : Good N [] := fun j hj => absurd hj (by simp)
theorem good_snoc (N : ℕ) (gs : List Gate) (g : Gate) (hg : Good N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (hi : ∀ i ∈ g.inputs, i < N + gs.length) : Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j gs.length with h | h
  · rw [List.getElem_append_left h]; exact hg j h
  · have : j = gs.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact ⟨hop, hl, hi⟩
theorem W_ext (gs gs' : List Gate) (h : ∃ t, gs' = gs ++ t) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : (Wr gs' x).getD i false = (Wr gs x).getD i false := by
  rw [W_take gs' x gs.length i hi]
  obtain ⟨t, rfl⟩ := h
  simp
theorem len_ext (gs gs' : List Gate) (h : ∃ t, gs' = gs ++ t) : gs.length ≤ gs'.length := by
  obtain ⟨t, rfl⟩ := h
  simp
theorem ext_tr {a b c : List Gate} (h1 : ∃ t, b = a ++ t) (h2 : ∃ t, c = b ++ t) : ∃ t, c = a ++ t := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t1 ++ t2, by simp⟩
theorem W_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (Wr (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (Wr gs x).getD i false) := by
  rw [W_snoc, stp]
  have := getD_app_m (Wr gs x) (g.op.eval (g.inputs.map fun i => (Wr gs x).getD i false))
  rw [W_len] at this
  exact this
theorem good_circ (N : ℕ) (gs : List Gate) (o : ℕ) (hg : Good N gs) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs, o⟩ ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, o⟩ := by
  constructor
  · intro g hgm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
    obtain ⟨h1, h2, _⟩ := hg j hj
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> rw [h] <;> simp
  · intro j hj i hi
    rw [gateAt_eq ⟨gs, o⟩ j hj] at hi
    exact (hg j hj).2.2 i hi
end Circ
section Fns
variable {n : ℕ}
def bt (i : Fin n) (x : Finset (Fin n)) : Bool := decide (i ∈ x)
def ng (i : Fin n) (x : Finset (Fin n)) : Bool := !(decide (i ∈ x))
def sm (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := (decide (e.1 ∈ x) == decide (e.2 ∈ x))
def ns (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x) == decide (e.2 ∈ x))
def k1 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x)) && !(decide (e.2 ∈ x))
def k2 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := decide (e.1 ∈ x) && !(decide (e.2 ∈ x))
def k3 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x)) && decide (e.2 ∈ x)
theorem b1 : ∀ p q : Bool, ((!p) && (p == q)) = ((!p) && !q) := by decide
theorem b2 : ∀ p q : Bool, (p && !(p == q)) = (p && !q) := by decide
theorem b3 : ∀ p q : Bool, ((!p) && !(p == q)) = ((!p) && q) := by decide
theorem b4 : ∀ p q : Bool, (((!p) && !q) || (p && !q)) = !q := by decide
theorem b5 : ∀ p q : Bool, ((!q) && (p == q)) = ((!p) && !q) := by decide
theorem b6 : ∀ p q : Bool, ((!q) && !(p == q)) = (p && !q) := by decide
theorem b7 : ∀ p q : Bool, (q && !(p == q)) = ((!p) && q) := by decide
theorem b8 : ∀ p q : Bool, (((!p) && !q) || ((!p) && q)) = !p := by decide
end Fns
section Build
variable {n : ℕ} (N : ℕ) (inp : Finset (Fin n) → List Bool)
def Av (gs : List Gate) (f : Finset (Fin n) → Bool) : Prop :=
  ∃ w < N + gs.length, ∀ x, (Wr gs (inp x)).getD w false = f x
theorem av_ext (hinp : ∀ x, (inp x).length = N) {gs gs' : List Gate} (h : ∃ t, gs' = gs ++ t)
    {f : Finset (Fin n) → Bool} (hf : Av N inp gs f) : Av N inp gs' f := by
  obtain ⟨w, hw, hv⟩ := hf
  have := len_ext gs gs' h
  refine ⟨w, by omega, fun x => ?_⟩
  rw [W_ext gs gs' h (inp x) w (by rw [hinp]; exact hw)]
  exact hv x
theorem av_congr {gs : List Gate} {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f)
    (e : ∀ x, f x = g x) : Av N inp gs g := by
  obtain ⟨w, hw, hv⟩ := hf
  exact ⟨w, hw, fun x => (hv x).trans (e x)⟩
theorem av_gate (hinp : ∀ x, (inp x).length = N) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    {gs : List Gate} (hg : Good N gs) {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f)
    (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => op.eval [f x, g x]) := by
  obtain ⟨w1, hw1, e1⟩ := hf
  obtain ⟨w2, hw2, e2⟩ := hg'
  refine ⟨gs ++ [⟨op, [w1, w2]⟩], good_snoc _ _ _ hg hop (by simp) ?_, ⟨_, rfl⟩, by simp,
    N + gs.length, by simp, fun x => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · have := W_last gs ⟨op, [w1, w2]⟩ (inp x)
    rw [hinp] at this
    rw [this]
    simp only [List.map_cons, List.map_nil, e1, e2]
theorem av_and (hinp : ∀ x, (inp x).length = N) {gs : List Gate} (hg : Good N gs)
    {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f) (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => f x && g x) := by
  obtain ⟨gs', h1, h2, h3, h4⟩ := av_gate N inp hinp GateOp.and (Or.inl rfl) hg hf hg'
  exact ⟨gs', h1, h2, h3, av_congr N inp h4 (fun x => by simp [GateOp.eval])⟩
theorem av_or (hinp : ∀ x, (inp x).length = N) {gs : List Gate} (hg : Good N gs)
    {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f) (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => f x || g x) := by
  obtain ⟨gs', h1, h2, h3, h4⟩ := av_gate N inp hinp GateOp.or (Or.inr rfl) hg hf hg'
  exact ⟨gs', h1, h2, h3, av_congr N inp h4 (fun x => by simp [GateOp.eval])⟩
variable (E : Finset (Fin n × Fin n)) (hinp : ∀ x, (inp x).length = N)
  (hb : ∀ gs i, Av N inp gs (bt i)) (hs : ∀ gs, ∀ e ∈ E, Av N inp gs (sm e))
  (hns : ∀ gs, ∀ e ∈ E, Av N inp gs (ns e))
include hinp hb hs hns in
theorem three_a {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n) (he : e ∈ E)
    (hA : Av N inp gs (ng e.1)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 3 ∧
      Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_and N inp hinp G hA (hs gs e he)
  obtain ⟨g2, G2, T2, L2, A2⟩ := av_and N inp hinp G1 (hb g1 e.1) (hns g1 e he)
  obtain ⟨g3, G3, T3, L3, A3⟩ := av_and N inp hinp G2 (av_ext N inp hinp (ext_tr T1 T2) hA) (hns g2 e he)
  refine ⟨g3, G3, ext_tr (ext_tr T1 T2) T3, by omega, ?_, ?_, ?_⟩
  · exact av_congr N inp (av_ext N inp hinp (ext_tr T2 T3) A1) (fun x => b1 _ _)
  · exact av_congr N inp (av_ext N inp hinp T3 A2) (fun x => b2 _ _)
  · exact av_congr N inp A3 (fun x => b3 _ _)
include hinp hb hs hns in
theorem three_b {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n) (he : e ∈ E)
    (hA : Av N inp gs (ng e.2)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 3 ∧
      Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_and N inp hinp G hA (hs gs e he)
  obtain ⟨g2, G2, T2, L2, A2⟩ := av_and N inp hinp G1 (av_ext N inp hinp T1 hA) (hns g1 e he)
  obtain ⟨g3, G3, T3, L3, A3⟩ := av_and N inp hinp G2 (hb g2 e.2) (hns g2 e he)
  refine ⟨g3, G3, ext_tr (ext_tr T1 T2) T3, by omega, ?_, ?_, ?_⟩
  · exact av_congr N inp (av_ext N inp hinp (ext_tr T2 T3) A1) (fun x => b5 _ _)
  · exact av_congr N inp (av_ext N inp hinp T3 A2) (fun x => b6 _ _)
  · exact av_congr N inp A3 (fun x => b7 _ _)
include hinp in
theorem one_a {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n)
    (h1 : Av N inp gs (k1 e)) (h2 : Av N inp gs (k2 e)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧ Av N inp gs' (ng e.2) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_or N inp hinp G h1 h2
  exact ⟨g1, G1, T1, L1, av_congr N inp A1 (fun x => b4 _ _)⟩
include hinp in
theorem one_b {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n)
    (h1 : Av N inp gs (k1 e)) (h3 : Av N inp gs (k3 e)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧ Av N inp gs' (ng e.1) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_or N inp hinp G h1 h3
  exact ⟨g1, G1, T1, L1, av_congr N inp A1 (fun x => b8 _ _)⟩
include hinp hb hs hns in
theorem build {c : ℕ} (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    (S : Finset (Fin n)) (hcov : ∀ j, ∃ i ∈ S, color i = j) :
    ∀ k (gs : List Gate) (K : Finset (Fin n)) (P : Finset (Fin n × Fin n)), (E \ P).card = k →
      Good N gs → S ⊆ K → P ⊆ E → (∀ v ∈ K, Av N inp gs (ng v)) →
      (∀ e ∈ P, Av N inp gs (k1 e) ∧ Av N inp gs (k2 e) ∧ Av N inp gs (k3 e) ∧ e.1 ∈ K ∧ e.2 ∈ K) →
      gs.length + S.card = K.card + 3 * P.card →
      ∃ gs', Good N gs' ∧ gs'.length + S.card = n + 3 * E.card ∧ (∀ v, Av N inp gs' (ng v)) ∧
        ∀ e ∈ E, Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro gs K P hk G hSK hPE hK hP hlen
    by_cases H : ∃ e ∈ E, e ∉ P ∧ (e.1 ∈ K ∨ e.2 ∈ K)
    · obtain ⟨e, he, heP, hor⟩ := H
      have hlt : (E \ insert e P).card < k := by
        rw [← hk, Finset.sdiff_insert]
        have hm : e ∈ E \ P := Finset.mem_sdiff.mpr ⟨he, heP⟩
        rw [Finset.card_erase_of_mem hm]
        have := Finset.card_pos.mpr ⟨e, hm⟩
        omega
      have hPE' : insert e P ⊆ E := Finset.insert_subset he hPE
      by_cases h1 : e.1 ∈ K
      · obtain ⟨g1, G1, T1, L1, A1, A2, A3⟩ := three_a N inp E hinp hb hs hns G e he (hK e.1 h1)
        by_cases h2 : e.2 ∈ K
        · refine ih _ hlt g1 K (insert e P) rfl G1 hSK hPE'
            (fun v hv => av_ext N inp hinp T1 (hK v hv)) (fun e' he' => ?_)
            (by rw [Finset.card_insert_of_notMem heP]; omega)
          rcases Finset.mem_insert.mp he' with rfl | he'
          · exact ⟨A1, A2, A3, h1, h2⟩
          · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
            exact ⟨av_ext N inp hinp T1 q1, av_ext N inp hinp T1 q2, av_ext N inp hinp T1 q3, q4, q5⟩
        · obtain ⟨g2, G2, T2, L2, B⟩ := one_a N inp hinp G1 e A1 A2
          refine ih _ hlt g2 (insert e.2 K) (insert e P) rfl G2 (hSK.trans (Finset.subset_insert _ _)) hPE'
            (fun v hv => ?_) (fun e' he' => ?_)
            (by rw [Finset.card_insert_of_notMem heP, Finset.card_insert_of_notMem h2]; omega)
          · rcases Finset.mem_insert.mp hv with rfl | hv
            · exact B
            · exact av_ext N inp hinp (ext_tr T1 T2) (hK v hv)
          · rcases Finset.mem_insert.mp he' with rfl | he'
            · exact ⟨av_ext N inp hinp T2 A1, av_ext N inp hinp T2 A2, av_ext N inp hinp T2 A3,
                Finset.mem_insert_of_mem h1, Finset.mem_insert_self _ _⟩
            · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
              exact ⟨av_ext N inp hinp (ext_tr T1 T2) q1, av_ext N inp hinp (ext_tr T1 T2) q2,
                av_ext N inp hinp (ext_tr T1 T2) q3, Finset.mem_insert_of_mem q4, Finset.mem_insert_of_mem q5⟩
      · have h2 : e.2 ∈ K := by rcases hor with h | h; exact absurd h h1; exact h
        obtain ⟨g1, G1, T1, L1, A1, A2, A3⟩ := three_b N inp E hinp hb hs hns G e he (hK e.2 h2)
        obtain ⟨g2, G2, T2, L2, B⟩ := one_b N inp hinp G1 e A1 A3
        refine ih _ hlt g2 (insert e.1 K) (insert e P) rfl G2 (hSK.trans (Finset.subset_insert _ _)) hPE'
          (fun v hv => ?_) (fun e' he' => ?_)
          (by rw [Finset.card_insert_of_notMem heP, Finset.card_insert_of_notMem h1]; omega)
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact B
          · exact av_ext N inp hinp (ext_tr T1 T2) (hK v hv)
        · rcases Finset.mem_insert.mp he' with rfl | he'
          · exact ⟨av_ext N inp hinp T2 A1, av_ext N inp hinp T2 A2, av_ext N inp hinp T2 A3,
              Finset.mem_insert_self _ _, Finset.mem_insert_of_mem h2⟩
          · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
            exact ⟨av_ext N inp hinp (ext_tr T1 T2) q1, av_ext N inp hinp (ext_tr T1 T2) q2,
              av_ext N inp hinp (ext_tr T1 T2) q3, Finset.mem_insert_of_mem q4, Finset.mem_insert_of_mem q5⟩
    · have hcl : ∀ e ∈ E, e.1 ∈ K ↔ e.2 ∈ K := by
        intro e he
        constructor
        · intro h1
          by_cases heP : e ∈ P
          · exact (hP e heP).2.2.2.2
          · exact absurd ⟨e, he, heP, Or.inl h1⟩ H
        · intro h2
          by_cases heP : e ∈ P
          · exact (hP e heP).2.2.2.1
          · exact absurd ⟨e, he, heP, Or.inr h2⟩ H
      have hcol := (hcomp K).mp hcl
      have hKu : ∀ v, v ∈ K := by
        intro v
        obtain ⟨i, hiS, hci⟩ := hcov (color v)
        exact (hcol i v hci).mp (hSK hiS)
      have hPu : ∀ e ∈ E, e ∈ P := by
        intro e he
        by_contra heP
        exact H ⟨e, he, heP, Or.inl (hKu e.1)⟩
      have hKc : K.card = n := by
        rw [Finset.eq_univ_of_forall hKu, Finset.card_univ, Fintype.card_fin]
      have hPE2 : P = E := Finset.Subset.antisymm hPE hPu
      refine ⟨gs, G, by rw [hlen, hKc, hPE2], fun v => hK v (hKu v), fun e he => ?_⟩
      obtain ⟨q1, q2, q3, _, _⟩ := hP e (hPu e he)
      exact ⟨q1, q2, q3⟩
end Build
section Facts
variable {n : ℕ}
theorem f_ng (i j : Fin n) (h : (ng i : Finset (Fin n) → Bool) = ng j) : i = j := by
  have h1 := congrFun h {i}
  simp [ng] at h1
  exact h1.symm
theorem f_k1 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k1 e = k1 e') : e = e' := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.2}
  simp [k1] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff] at h1 h2
  omega
theorem f_k2 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = k2 e') : e = e' := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e'.2}
  simp [k2, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_k3 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k3 e = k3 e') : e = e' := by
  have h1 := congrFun h {e.2}
  have h2 := congrFun h {e.2, e'.1}
  simp [k3, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_ng_k1 (i : Fin n) (e : Fin n × Fin n) (he : e.1 < e.2) (h : ng i = k1 e) : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.2}
  simp [ng, k1] at h1 h2
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1 h2
  omega
theorem f_ng_k2 (i : Fin n) (e : Fin n × Fin n) (h : ng i = k2 e) : False := by
  have h1 := congrFun h ∅
  simp [ng, k2] at h1
theorem f_ng_k3 (i : Fin n) (e : Fin n × Fin n) (h : ng i = k3 e) : False := by
  have h1 := congrFun h ∅
  simp [ng, k3] at h1
theorem f_k1_k2 (e e' : Fin n × Fin n) (h : k1 e = k2 e') : False := by
  have h1 := congrFun h ∅
  simp [k1, k2] at h1
theorem f_k1_k3 (e e' : Fin n × Fin n) (h : k1 e = k3 e') : False := by
  have h1 := congrFun h ∅
  simp [k1, k3] at h1
theorem f_k2_k3 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = k3 e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e'.1}
  simp [k2, k3, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_k2_ns (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = ns e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e.2}
  have h3 := congrFun h {e.2}
  simp [k2, ns, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2 h3
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2 h3
  try (rw [Bool.eq_iff_iff] at h1)
  try (rw [Bool.eq_iff_iff] at h2)
  try (rw [Bool.eq_iff_iff] at h3)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, iff_iff_implies_and_implies] at h1 h2 h3
  omega
theorem f_k3_ns (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k3 e = ns e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e.2}
  have h3 := congrFun h {e.2}
  simp [k3, ns, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2 h3
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2 h3
  try (rw [Bool.eq_iff_iff] at h1)
  try (rw [Bool.eq_iff_iff] at h2)
  try (rw [Bool.eq_iff_iff] at h3)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, iff_iff_implies_and_implies] at h1 h2 h3
  omega
theorem f_k2_0 (e : Fin n × Fin n) (he : e.1 < e.2) (h : k2 e = fun _ => false) : False := by
  have h1 := congrFun h {e.1}
  simp [k2] at h1
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1
  omega
theorem f_k3_0 (e : Fin n × Fin n) (he : e.1 < e.2) (h : k3 e = fun _ => false) : False := by
  have h1 := congrFun h {e.2}
  simp [k3] at h1
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1
  omega
end Facts
section Main
variable {n : ℕ}
def RAW [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n) → Bool) :=
  {fun _ => false, fun _ => true} ∪ Finset.univ.image bt ∪ E.image sm ∪ E.image ns
def NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n) → Bool) :=
  Finset.univ.image ng ∪ E.image k1 ∪ E.image k2 ∪ E.image k3
theorem mem_NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (f : Finset (Fin n) → Bool) :
    f ∈ NEED E ↔ (∃ i, ng i = f) ∨ (∃ e ∈ E, k1 e = f) ∨ (∃ e ∈ E, k2 e = f) ∨ (∃ e ∈ E, k3 e = f) := by
  simp only [NEED, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, or_assoc]
theorem mem_RAW [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (f : Finset (Fin n) → Bool) :
    f ∈ RAW E ↔ f = (fun _ => false) ∨ f = (fun _ => true) ∨ (∃ i, bt i = f) ∨ (∃ e ∈ E, sm e = f) ∨
      (∃ e ∈ E, ns e = f) := by
  simp only [RAW, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and, or_assoc]
theorem card_NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2) : n + 3 * E.card ≤ (NEED E).card := by
  have i0 : (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool)).card = n := by
    rw [Finset.card_image_of_injective _ (fun i j h => f_ng i j h), Finset.card_univ, Fintype.card_fin]
  have i1 : (E.image k1).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k1 e e' (hE e he) (hE e' he') h)
  have i2 : (E.image k2).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k2 e e' (hE e he) (hE e' he') h)
  have i3 : (E.image k3).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k3 e e' (hE e he) (hE e' he') h)
  have d1 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool)) (E.image k1) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨i, rfl⟩ := hf
    obtain ⟨e, he, h⟩ := hf'
    exact f_ng_k1 i e (hE e he) h.symm
  have d2 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool) ∪ E.image k1) (E.image k2) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨e', he', rfl⟩ := hf'
    rcases hf with ⟨i, h⟩ | ⟨e, he, h⟩
    · exact f_ng_k2 i e' h
    · exact f_k1_k2 e e' h
  have d3 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool) ∪ E.image k1 ∪ E.image k2)
      (E.image k3) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨e', he', rfl⟩ := hf'
    rcases hf with (⟨i, h⟩ | ⟨e, he, h⟩) | ⟨e, he, h⟩
    · exact f_ng_k3 i e' h
    · exact f_k1_k3 e e' h
    · exact f_k2_k3 e e' (hE e he) (hE e' he') h
  unfold NEED
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    i0, i1, i2, i3]
  omega
theorem edge_col {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) : ∀ e ∈ E, color e.1 = color e.2 := by
  intro e he
  have h := (hcomp (Finset.univ.filter (fun j => color j = color e.1))).mpr (by
    intro i j hij
    simp [hij])
  have h2 : e.2 ∈ Finset.univ.filter (fun j => color j = color e.1) := (h e he).mp (by simp)
  rw [Finset.mem_filter] at h2
  exact h2.2.symm
theorem iso_col {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) (i : Fin n) (hi : ∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i) :
    ∀ j, color j = color i → j = i := by
  intro j hj
  have h := (hcomp {i}).mp (by
    intro e he
    simp [(hi e he).1, (hi e he).2])
  have := (h i j hj.symm).mp (by simp)
  simpa using this
theorem suff [DecidableEq (Finset (Fin n) → Bool)] {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hE : ∀ e ∈ E, e.1 < e.2) (hsurj : Function.Surjective color)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    (A : Finset (Finset (Fin n)))
    (hF : ∀ κ : Fin c, ∃ y ∈ A, (∀ v ∈ y, color v ≠ κ) ∧ y ∪ Finset.univ.filter (fun v => color v = κ) ∈ A)
    (hD : ∀ f ∈ NEED E, ∀ g ∈ NEED E, f ≠ g → ∃ x ∈ A, f x ≠ g x)
    (hR : ∀ f ∈ NEED E, ∀ g ∈ RAW E, ∃ x ∈ A, f x ≠ g x)
    (S : Finset (Fin n)) (p : ℕ) :
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (RAW E ∪ S.image ng).toList.length C ∧
      C.output < (RAW E ∪ S.image ng).toList.length + C.size ∧ C.size ≤ p ∧
      ∀ f ∈ NEED E, ∃ j < (RAW E ∪ S.image ng).toList.length + C.size,
        ∀ x ∈ A, (C.wires ((RAW E ∪ S.image ng).toList.map (fun g => g x))).getD j false = f x) ↔
    ((∀ j, ∃ i ∈ S, color i = j) ∧ n + 3 * E.card - S.card ≤ p) := by
  set L := (RAW E ∪ S.image ng).toList with hL
  have memL : ∀ g, g ∈ L ↔ g ∈ RAW E ∪ S.image ng := fun g => Finset.mem_toList
  have getL : ∀ (x : Finset (Fin n)) (i : ℕ) (hi : i < L.length),
      (L.map (fun g => g x)).getD i false = (L[i]) x := by
    intro x i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  have hec := edge_col E color hcomp
  have hSN : ∀ i ∈ S, ng i ∈ NEED E := fun i _ => (mem_NEED E _).mpr (Or.inl ⟨i, rfl⟩)
  constructor
  · rintro ⟨C, hm, hrb, hout, hp, hw⟩
    have hm' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have := (hm g hg).1
      simpa using this
    refine ⟨?_, ?_⟩
    · intro κ
      by_contra hno
      have hno' : ∀ i ∈ S, color i ≠ κ := fun i hi hc => hno ⟨i, hi, hc⟩
      obtain ⟨y, hyA, hy, hzA⟩ := hF κ
      set z := y ∪ Finset.univ.filter (fun v => color v = κ) with hz
      have zin : ∀ v, color v = κ → v ∈ z := fun v hv => by simp [z, hv]
      have zout : ∀ v, color v ≠ κ → (v ∈ z ↔ v ∈ y) := fun v hv => by simp [z, hv]
      have yout : ∀ v, color v = κ → v ∉ y := fun v hv hvy => hy v hvy hv
      obtain ⟨i0, hi0⟩ := hsurj κ
      obtain ⟨j, _, hjv⟩ := hw (ng i0) ((mem_NEED E _).mpr (Or.inl ⟨i0, rfl⟩))
      have mono_inp : ∀ g ∈ RAW E ∪ S.image ng, g y = true → g z = true := by
        intro g hg hgy
        rcases Finset.mem_union.mp hg with hg | hg
        · rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
          · simp at hgy
          · rfl
          · simp only [bt, decide_eq_true_eq] at hgy ⊢
            exact Finset.mem_union_left _ hgy
          · by_cases hc : color e.1 = κ
            · have h2 : color e.2 = κ := (hec e he).symm.trans hc
              simp [sm, zin _ hc, zin _ h2]
            · have h2 : color e.2 ≠ κ := fun h => hc ((hec e he).trans h)
              simp only [sm] at hgy ⊢
              have a1 := zout _ hc
              have a2 := zout _ h2
              by_cases q1 : e.1 ∈ y <;> by_cases q2 : e.2 ∈ y <;> simp_all
          · by_cases hc : color e.1 = κ
            · have h2 : color e.2 = κ := (hec e he).symm.trans hc
              simp [ns, yout _ hc, yout _ h2] at hgy
            · have h2 : color e.2 ≠ κ := fun h => hc ((hec e he).trans h)
              simp only [ns] at hgy ⊢
              have a1 := zout _ hc
              have a2 := zout _ h2
              by_cases q1 : e.1 ∈ y <;> by_cases q2 : e.2 ∈ y <;> simp_all
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
          have hc := hno' i hi
          simp only [ng, Bool.not_eq_true', decide_eq_false_iff_not] at hgy ⊢
          rwa [zout i hc]
      have hle : ∀ i, (L.map (fun g => g y)).getD i false = true → (L.map (fun g => g z)).getD i false = true := by
        intro i hi
        by_cases hiN : i < L.length
        · rw [getL y i hiN] at hi
          rw [getL z i hiN]
          exact mono_inp _ ((memL _).mp (List.getElem_mem hiN)) hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          exact absurd hi (by decide)
      have hmono := W_mono C.gates hm' (L.map (fun g => g y)) (L.map (fun g => g z)) (by simp) hle j
      have e1 := hjv y hyA
      have e2 := hjv z hzA
      have hy0 : ng i0 y = true := by
        simp only [ng, Bool.not_eq_true', decide_eq_false_iff_not]
        exact yout i0 hi0
      have hz0 : ng i0 z = false := by
        simp only [ng, Bool.not_eq_false', decide_eq_true_eq]
        exact zin i0 hi0
      rw [hy0] at e1
      rw [hz0] at e2
      have := hmono e1
      rw [show (Wr C.gates (L.map (fun g => g z))).getD j false = false from e2] at this
      exact absurd this (by decide)
    · choose! jf hjf hjv using hw
      have h1 : ∀ f ∈ NEED E \ S.image ng, L.length ≤ jf f := by
        intro f hf
        rw [Finset.mem_sdiff] at hf
        by_contra hlt
        rw [not_le] at hlt
        have hg : L[jf f] ∈ RAW E ∪ S.image ng := (memL _).mp (List.getElem_mem hlt)
        have heq : ∀ x ∈ A, f x = (L[jf f]) x := by
          intro x hx
          rw [← hjv f hf.1 x hx, ← getL x _ hlt]
          exact W_lt C.gates _ _ (by simpa using hlt)
        rcases Finset.mem_union.mp hg with hgR | hgS
        · obtain ⟨x, hx, hne⟩ := hR f hf.1 _ hgR
          exact hne (heq x hx)
        · obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hgS
          have hgN : L[jf f] ∈ NEED E := hgi ▸ hSN i hi
          have hfg : f ≠ L[jf f] := by
            intro h
            exact hf.2 (h ▸ hgS)
          obtain ⟨x, hx, hne⟩ := hD f hf.1 _ hgN hfg
          exact hne (heq x hx)
      have h2 : Set.InjOn jf (↑(NEED E \ S.image ng) : Set (Finset (Fin n) → Bool)) := by
        intro f hf g hg hfg
        have hf' := (Finset.mem_sdiff.mp hf).1
        have hg' := (Finset.mem_sdiff.mp hg).1
        by_contra hne
        obtain ⟨x, hx, hne'⟩ := hD f hf' g hg' hne
        apply hne'
        rw [← hjv f hf' x hx, ← hjv g hg' x hx, hfg]
      have h3 : (NEED E \ S.image ng).card ≤ (Finset.Ico L.length (L.length + C.size)).card := by
        apply Finset.card_le_card_of_injOn jf _ h2
        intro f hf
        have hf' := (Finset.mem_sdiff.mp hf).1
        exact Finset.mem_Ico.mpr ⟨h1 f hf, hjf f hf'⟩
      rw [Nat.card_Ico] at h3
      have h4 : (NEED E).card - (S.image ng).card ≤ (NEED E \ S.image ng).card := Finset.le_card_sdiff _ _
      have h5 : (S.image ng).card ≤ S.card := Finset.card_image_le
      have h6 := card_NEED E hE
      omega
  · rintro ⟨hcov, hp⟩
    have hinp : ∀ x : Finset (Fin n), (L.map (fun g => g x)).length = L.length := by simp
    have avin : ∀ gs, ∀ g ∈ RAW E ∪ S.image ng, Av L.length (fun x => L.map (fun g => g x)) gs g := by
      intro gs g hg
      have hgL : g ∈ L := (memL g).mpr hg
      have hlt : L.idxOf g < L.length := List.idxOf_lt_length_iff.mpr hgL
      refine ⟨L.idxOf g, by omega, fun x => ?_⟩
      rw [W_lt _ _ _ (by simpa using hlt), getL x _ hlt, List.getElem_idxOf]
    have hb : ∀ gs i, Av L.length (fun x => L.map (fun g => g x)) gs (bt i) := fun gs i =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))
    have hs : ∀ gs, ∀ e ∈ E, Av L.length (fun x => L.map (fun g => g x)) gs (sm e) := fun gs e he =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, rfl⟩))))))
    have hns : ∀ gs, ∀ e ∈ E, Av L.length (fun x => L.map (fun g => g x)) gs (ns e) := fun gs e he =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))))))
    have hsn : ∀ gs, ∀ i ∈ S, Av L.length (fun x => L.map (fun g => g x)) gs (ng i) := fun gs i hi =>
      avin gs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem ng hi))
    obtain ⟨gs, G, hlen, hv, hev⟩ := build L.length (fun x => L.map (fun g => g x)) E hinp hb hs hns color hcomp
      S hcov _ [] S ∅ rfl (good_nil _) (Finset.Subset.refl _) (Finset.empty_subset _)
      (fun v hv => hsn [] v hv) (by simp) (by simp)
    have hL0 : 0 < L.length := by
      apply List.length_pos_of_mem (a := fun _ => false)
      rw [memL]
      exact Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inl rfl))
    obtain ⟨m2, rb⟩ := good_circ L.length gs 0 G
    refine ⟨⟨gs, 0⟩, m2, rb, by simp [Circuit.size]; omega, by simp [Circuit.size]; omega, ?_⟩
    intro f hf
    rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · obtain ⟨w, hw, hval⟩ := hv i
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).1
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).2.1
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).2.2
      exact ⟨w, hw, fun x _ => hval x⟩
end Main
section Wrap
variable {n : ℕ}
theorem suffA {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hE : ∀ e ∈ E, e.1 < e.2) (hsurj : Function.Surjective color)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    {dq : DecidableEq (Finset (Fin n) → Bool)}
    (bit neg : Fin n → Finset (Fin n) → Bool) (same : Fin n × Fin n → Finset (Fin n) → Bool)
    (hbit : ∀ i x, bit i x = true ↔ i ∈ x) (hneg : ∀ i x, neg i x = !(bit i x))
    (hsame : ∀ e x, same e x = (bit e.1 x == bit e.2 x))
    (raw need : Finset (Finset (Fin n) → Bool))
    (hraw : raw = {fun _ => false, fun _ => true} ∪ Finset.univ.image bit ∪ E.image same ∪
      E.image (fun e x => !(same e x)))
    (hneed : need = Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
      E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x))
    (A : Finset (Finset (Fin n)))
    (hF : ∀ κ : Fin c, ∃ y ∈ A, (∀ v ∈ y, color v ≠ κ) ∧ y ∪ Finset.univ.filter (fun v => color v = κ) ∈ A)
    (hD : ∀ f ∈ need, ∀ g ∈ need, f ≠ g → ∃ x ∈ A, f x ≠ g x)
    (hR : ∀ f ∈ need, ∀ g ∈ raw, ∃ x ∈ A, f x ≠ g x) :
    ∀ (S : Finset (Fin n)) (p : ℕ),
      (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (raw ∪ S.image neg).toList.length C ∧
        C.output < (raw ∪ S.image neg).toList.length + C.size ∧ C.size ≤ p ∧
        ∀ f ∈ need, ∃ j < (raw ∪ S.image neg).toList.length + C.size,
          ∀ x ∈ A, (C.wires ((raw ∪ S.image neg).toList.map (fun g => g x))).getD j false = f x) ↔
      ((∀ j, ∃ i ∈ S, color i = j) ∧ n + 3 * E.card - S.card ≤ p) := by
  have hb : bit = bt := by
    funext i x
    exact Bool.eq_iff_iff.mpr (by rw [hbit]; simp [bt])
  subst hb
  have hn : neg = ng := by
    funext i x
    rw [hneg]
    rfl
  subst hn
  have hs : same = sm := by
    funext e x
    rw [hsame]
    rfl
  subst hs
  subst hraw
  subst hneed
  exact fun S p => suff E color hE hsurj hcomp A hF hD hR S p
end Wrap
section Nec
theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = Wr C.gates x := rfl
def Has {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f : α → Bool) : Prop :=
  ∃ j < L.length + gs.length, ∀ x ∈ A, (Wr gs (L.map fun g => g x)).getD j false = f x
theorem map_getD {α : Type} (L : List (α → Bool)) (x : α) (j : ℕ) (hj : j < L.length) :
    (L.map fun g => g x).getD j false = L[j] x := by
  simp [List.getD_eq_getElem?_getD, hj]
theorem has_inp {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (g : α → Bool)
    (hg : g ∈ L) : Has L A gs g := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  refine ⟨j, by omega, fun x _ => ?_⟩
  rw [W_lt _ _ _ (by simpa using hj)]
  exact map_getD L x j hj
theorem has_ext {α : Type} (L : List (α → Bool)) (A : Finset α) (gs u : List Gate) (f : α → Bool)
    (h : Has L A gs f) : Has L A (gs ++ u) f := by
  obtain ⟨j, hj, hv⟩ := h
  refine ⟨j, by simp; omega, fun x hx => ?_⟩
  rw [W_ext gs (gs ++ u) ⟨u, rfl⟩ _ _ (by simpa using hj)]
  exact hv x hx
theorem has_congr {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f f' : α → Bool)
    (h : Has L A gs f) (he : ∀ x ∈ A, f x = f' x) : Has L A gs f' := by
  obtain ⟨j, hj, hv⟩ := h
  exact ⟨j, hj, fun x hx => (hv x hx).trans (he x hx)⟩
theorem has_gate {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f1 f2 : α → Bool)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (hg : Good L.length gs)
    (h1 : Has L A gs f1) (h2 : Has L A gs f2) :
    ∃ g : Gate, Good L.length (gs ++ [g]) ∧ Has L A (gs ++ [g]) (fun x => op.eval [f1 x, f2 x]) := by
  obtain ⟨j1, hj1, v1⟩ := h1
  obtain ⟨j2, hj2, v2⟩ := h2
  refine ⟨⟨op, [j1, j2]⟩, good_snoc _ _ _ hg hop (by simp) (by intro i hi; simp at hi; omega),
    L.length + gs.length, by simp, fun x hx => ?_⟩
  have := W_last gs ⟨op, [j1, j2]⟩ (L.map fun g => g x)
  rw [List.length_map] at this
  rw [this]
  show op.eval [(Wr gs (L.map fun g => g x)).getD j1 false, (Wr gs (L.map fun g => g x)).getD j2 false] = _
  rw [v1 x hx, v2 x hx]
theorem has_const {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (v : Bool)
    (hg : Good L.length gs) :
    ∃ g : Gate, Good L.length (gs ++ [g]) ∧ Has L A (gs ++ [g]) (fun _ => v) := by
  refine ⟨⟨if v then GateOp.and else GateOp.or, []⟩,
    good_snoc _ _ _ hg (by cases v <;> simp) (by simp) (by simp), L.length + gs.length, by simp,
    fun x _ => ?_⟩
  have := W_last gs ⟨if v then GateOp.and else GateOp.or, []⟩ (L.map fun g => g x)
  rw [List.length_map] at this
  rw [this]
  cases v <;> simp [GateOp.eval]
theorem level {α ι : Type} [DecidableEq ι] (L : List (α → Bool)) (A : Finset α) (φ : ι → α → Bool)
    (gs0 : List Gate) (T : Finset ι)
    (hT : ∀ t ∈ T, ∃ op : GateOp, ∃ f1 f2 : α → Bool, (op = GateOp.and ∨ op = GateOp.or) ∧
      Has L A gs0 f1 ∧ Has L A gs0 f2 ∧ ∀ x ∈ A, φ t x = op.eval [f1 x, f2 x]) :
    ∀ gs, Good L.length gs → (∃ u, gs = gs0 ++ u) → ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧
      gs'.length ≤ gs.length + T.card ∧ ∀ t ∈ T, Has L A gs' (φ t) := by
  induction T using Finset.induction_on with
  | empty => intro gs hg _; exact ⟨gs, hg, ⟨[], by simp⟩, by simp, by simp⟩
  | @insert t0 T ht0 ih =>
    intro gs hg hgs
    obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hl1, hh1⟩ :=
      ih (fun t ht => hT t (Finset.mem_insert_of_mem ht)) gs hg hgs
    obtain ⟨op, f1, f2, hop, h1, h2, he⟩ := hT t0 (Finset.mem_insert_self _ _)
    obtain ⟨u0, rfl⟩ := hgs
    have h1' : Has L A (gs0 ++ u0 ++ u1) f1 := by
      rw [List.append_assoc]; exact has_ext L A gs0 (u0 ++ u1) f1 h1
    have h2' : Has L A (gs0 ++ u0 ++ u1) f2 := by
      rw [List.append_assoc]; exact has_ext L A gs0 (u0 ++ u1) f2 h2
    obtain ⟨g, hg2, hh2⟩ := has_gate L A _ f1 f2 op hop hg1 h1' h2'
    refine ⟨_, hg2, ⟨u1 ++ [g], by simp⟩, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hl1 ⊢
      rw [Finset.card_insert_of_notMem ht0]; omega
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact has_congr L A _ _ _ hh2 (fun x hx => (he x hx).symm)
      · exact has_ext L A _ [g] _ (hh1 t ht)
def Bld {α : Type} (L : List (α → Bool)) (A : Finset α) (f : α → Bool) : Prop :=
  ∀ gs, Good L.length gs → ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧ Has L A gs' f
theorem bld_inp {α : Type} (L : List (α → Bool)) (A : Finset α) (g : α → Bool) (hg : g ∈ L) :
    Bld L A g := fun gs hgs => ⟨gs, hgs, ⟨[], by simp⟩, has_inp L A gs g hg⟩
theorem bld_bin {α : Type} (L : List (α → Bool)) (A : Finset α) (f1 f2 : α → Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (h1 : Bld L A f1) (h2 : Bld L A f2) :
    Bld L A (fun x => op.eval [f1 x, f2 x]) := by
  intro gs hgs
  obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hh1⟩ := h1 gs hgs
  obtain ⟨gs2, hg2, ⟨u2, rfl⟩, hh2⟩ := h2 _ hg1
  obtain ⟨g, hg3, hh3⟩ := has_gate L A _ f1 f2 op hop hg2 (has_ext L A _ u2 f1 hh1) hh2
  exact ⟨_, hg3, ⟨u1 ++ u2 ++ [g], by simp⟩, hh3⟩
theorem bld_const {α : Type} (L : List (α → Bool)) (A : Finset α) (v : Bool) :
    Bld L A (fun _ => v) := by
  intro gs hgs
  obtain ⟨g, hg, hh⟩ := has_const L A gs v hgs
  exact ⟨_, hg, ⟨[g], rfl⟩, hh⟩
theorem bld_congr {α : Type} (L : List (α → Bool)) (A : Finset α) (f f' : α → Bool) (h : Bld L A f)
    (he : ∀ x ∈ A, f x = f' x) : Bld L A f' := by
  intro gs hgs
  obtain ⟨gs', h1, h2, h3⟩ := h gs hgs
  exact ⟨gs', h1, h2, has_congr L A _ _ _ h3 he⟩
theorem bld_andL {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : Bld L A (fun x => l.all (fun g => g x)) := by
  induction l with
  | nil => exact bld_congr L A _ _ (bld_const L A true) (fun x _ => by simp)
  | cons g0 l ih =>
    have := bld_bin L A _ _ GateOp.and (Or.inl rfl) (hl g0 (by simp))
      (ih (fun g hg => hl g (by simp [hg])))
    exact bld_congr L A _ _ this (fun x _ => by simp [GateOp.eval])
theorem bld_orL {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : Bld L A (fun x => l.any (fun g => g x)) := by
  induction l with
  | nil => exact bld_congr L A _ _ (bld_const L A false) (fun x _ => by simp)
  | cons g0 l ih =>
    have := bld_bin L A _ _ GateOp.or (Or.inr rfl) (hl g0 (by simp))
      (ih (fun g hg => hl g (by simp [hg])))
    exact bld_congr L A _ _ this (fun x _ => by simp [GateOp.eval])
theorem bld_all {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : ∀ gs, Good L.length gs →
    ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧ ∀ g ∈ l, Has L A gs' g := by
  induction l with
  | nil => intro gs hgs; exact ⟨gs, hgs, ⟨[], by simp⟩, by simp⟩
  | cons g0 l ih =>
    intro gs hgs
    obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hh1⟩ := ih (fun g hg => hl g (by simp [hg])) gs hgs
    obtain ⟨gs2, hg2, ⟨u2, rfl⟩, hh2⟩ := hl g0 (by simp) _ hg1
    refine ⟨_, hg2, ⟨u1 ++ u2, by simp⟩, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hh2
    · exact has_ext L A _ u2 g (hh1 g hg)
theorem bld_sep {α : Type} (L : List (α → Bool)) (A : Finset α)
    (hsep : ∀ y ∈ A, ∀ x ∈ A, (∀ g ∈ L, g y = true → g x = true) → y = x) (f : α → Bool) :
    Bld L A f := by
  have ho := bld_orL L A ((A.toList.filter (fun y => f y)).map
    (fun y => fun x => (L.filter (fun g => g y)).all (fun g => g x)))
    (fun h hh => by
      simp only [List.mem_map] at hh
      obtain ⟨y, _, rfl⟩ := hh
      exact bld_andL L A _ (fun g hg => bld_inp L A g (List.mem_filter.mp hg).1))
  refine bld_congr L A _ _ ho (fun x hx => ?_)
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, Finset.mem_toList]
  constructor
  · rintro ⟨h, ⟨y, ⟨hy, hfy⟩, rfl⟩, hyx⟩
    simp only [List.all_eq_true, List.mem_filter] at hyx
    have := hsep y hy x hx (fun g hg hgy => hyx g ⟨hg, hgy⟩)
    subst this; exact hfy
  · intro hfx
    refine ⟨_, ⟨x, ⟨hx, hfx⟩, rfl⟩, ?_⟩
    simp only [List.all_eq_true, List.mem_filter]
    exact fun g hg => hg.2
theorem pack {α : Type} (L : List (α → Bool)) (A : Finset α) (need : Finset (α → Bool)) (gs : List Gate)
    (hg : Good L.length gs) (hL0 : 0 < L.length) (hh : ∀ f ∈ need, Has L A gs f) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length + C.size ∧ C.size = gs.length ∧ ∀ f ∈ need, ∃ j < L.length + C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
  refine ⟨⟨gs, 0⟩, ?_, ?_, ?_, rfl, ?_⟩
  · intro g hgm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
    obtain ⟨h1, h2, _⟩ := hg j hj
    exact ⟨by rcases h1 with h | h <;> simp [h], h2⟩
  · intro j hj i hi
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j = gs[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    rw [e] at hi
    exact (hg j hj).2.2 i hi
  · simp only [Circuit.size]; omega
  · intro f hf
    exact hh f hf
end Nec
section Nec2
variable {n : ℕ}
def KP [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (A : Finset (Finset (Fin n))) : Prop :=
  ∀ (S : Finset (Fin n)) (p : ℕ),
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (RAW E ∪ S.image ng).toList.length C ∧
      C.output < (RAW E ∪ S.image ng).toList.length + C.size ∧ C.size ≤ p ∧
      ∀ f ∈ NEED E, ∃ j < (RAW E ∪ S.image ng).toList.length + C.size,
        ∀ x ∈ A, (C.wires ((RAW E ∪ S.image ng).toList.map (fun g => g x))).getD j false = f x) ↔
    (S.Nonempty ∧ n + 3 * E.card - S.card ≤ p)
theorem nec_uni [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (hconn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ)
    (A : Finset (Finset (Fin n))) (hk : KP E A) : ∅ ∈ A ∧ Finset.univ ∈ A := by
  by_contra hno
  have memL : ∀ g, g ∈ (RAW E ∪ (∅ : Finset (Fin n)).image ng).toList ↔
      g ∈ RAW E ∪ (∅ : Finset (Fin n)).image ng := fun g => Finset.mem_toList
  have hsep : ∀ y ∈ A, ∀ x ∈ A, (∀ g ∈ (RAW E ∪ (∅ : Finset (Fin n)).image ng).toList,
      g y = true → g x = true) → y = x := by
    intro y hy x hx hyx
    have hr : ∀ g ∈ RAW E, g y = true → g x = true :=
      fun g hg => hyx g ((memL g).mpr (Finset.mem_union_left _ hg))
    have hb : ∀ v, v ∈ y → v ∈ x := by
      intro v hv
      have := hr (bt v) ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩)))) (by simp [bt, hv])
      simpa [bt] using this
    have hs : ∀ e ∈ E, ((e.1 ∈ y ↔ e.2 ∈ y) ↔ (e.1 ∈ x ↔ e.2 ∈ x)) := by
      intro e he
      have h1 := hr (sm e) ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, rfl⟩)))))
      have h2 := hr (ns e) ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩)))))
      simp only [sm, ns] at h1 h2
      by_cases a1 : e.1 ∈ y <;> by_cases a2 : e.2 ∈ y <;> by_cases a3 : e.1 ∈ x <;>
        by_cases a4 : e.2 ∈ x <;> simp_all
    have hZ := hconn (x \ y) (by
      intro e he
      have h0 := hs e he
      have b1 := hb e.1
      have b2 := hb e.2
      simp only [Finset.mem_sdiff]
      tauto)
    rcases hZ with hZ | hZ
    · have hxy : x ⊆ y := by
        intro v hv
        by_contra hvy
        have h3 : v ∈ x \ y := Finset.mem_sdiff.mpr ⟨hv, hvy⟩
        rw [hZ] at h3
        simp at h3
      exact Finset.Subset.antisymm (fun v hv => hb v hv) hxy
    · exfalso
      apply hno
      have hall : ∀ v, v ∈ x ∧ v ∉ y := by
        intro v
        have h3 : v ∈ x \ y := by rw [hZ]; exact Finset.mem_univ v
        exact Finset.mem_sdiff.mp h3
      have hy0 : y = ∅ := by
        ext v
        simp [(hall v).2]
      have hx1 : x = Finset.univ := by
        ext v
        simp [(hall v).1]
      exact ⟨hy0 ▸ hy, hx1 ▸ hx⟩
  have hb_all : ∀ f ∈ (NEED E).toList, Bld (RAW E ∪ (∅ : Finset (Fin n)).image ng).toList A f :=
    fun f _ => bld_sep _ A hsep f
  obtain ⟨gs, hgs, _, hh⟩ := bld_all _ A (NEED E).toList hb_all [] (fun j hj => absurd hj (by simp))
  have hL0 : 0 < (RAW E ∪ (∅ : Finset (Fin n)).image ng).toList.length :=
    List.length_pos_of_mem ((memL _).mpr (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inl rfl))))
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := pack _ A (NEED E) gs hgs hL0
    (fun f hf => hh f (Finset.mem_toList.mpr hf))
  have := ((hk ∅ C.size).mp ⟨C, h1, h2, h3, le_refl _, h5⟩).1
  simp at this
def kk (e : Fin n × Fin n) : Option Bool → Finset (Fin n) → Bool
  | none => k1 e
  | some true => k2 e
  | some false => k3 e
theorem cheap [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (A : Finset (Finset (Fin n))) (hk : KP E A) (k0 : (Fin n × Fin n) × Option Bool) (hk0 : k0.1 ∈ E)
    (g : Finset (Fin n) → Bool)
    (hg : g ∈ RAW E ∨ ∃ k' : (Fin n × Fin n) × Option Bool, k'.1 ∈ E ∧ k' ≠ k0 ∧ g = kk k'.1 k'.2)
    (heq : ∀ x ∈ A, kk k0.1 k0.2 x = g x) : False := by
  have memL : ∀ g, g ∈ (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList ↔
      g ∈ RAW E ∪ (Finset.univ : Finset (Fin n)).image ng := fun g => Finset.mem_toList
  have hraw : ∀ g ∈ RAW E, g ∈ (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList :=
    fun g hg => (memL g).mpr (Finset.mem_union_left _ hg)
  have hneg : ∀ v, ng v ∈ (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList :=
    fun v => (memL _).mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
  have hbit : ∀ v, bt v ∈ (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList :=
    fun v => hraw _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
  have hT : ∀ k ∈ (E ×ˢ (Finset.univ : Finset (Option Bool))).erase k0, ∃ op : GateOp,
      ∃ f1 f2 : Finset (Fin n) → Bool,
      (op = GateOp.and ∨ op = GateOp.or) ∧
      Has (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList A [] f1 ∧
      Has (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList A [] f2 ∧
      ∀ x ∈ A, (fun k : (Fin n × Fin n) × Option Bool => kk k.1 k.2) k x = op.eval [f1 x, f2 x] := by
    rintro ⟨e, o⟩ _
    rcases o with _ | ⟨_ | _⟩
    · exact ⟨GateOp.and, ng e.1, ng e.2, Or.inl rfl, has_inp _ _ _ _ (hneg _),
        has_inp _ _ _ _ (hneg _), fun x _ => by simp [kk, k1, ng, GateOp.eval]⟩
    · exact ⟨GateOp.and, ng e.1, bt e.2, Or.inl rfl, has_inp _ _ _ _ (hneg _),
        has_inp _ _ _ _ (hbit _), fun x _ => by simp [kk, k3, ng, bt, GateOp.eval]⟩
    · exact ⟨GateOp.and, bt e.1, ng e.2, Or.inl rfl, has_inp _ _ _ _ (hbit _),
        has_inp _ _ _ _ (hneg _), fun x _ => by simp [kk, k2, ng, bt, GateOp.eval]⟩
  obtain ⟨gs, hgs, _, hlen, hh⟩ := level _ A (fun k : (Fin n × Fin n) × Option Bool => kk k.1 k.2)
    [] _ hT [] (fun j hj => absurd hj (by simp)) ⟨[], rfl⟩
  have hk0' : Has (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList A gs (kk k0.1 k0.2) := by
    rcases hg with hg | ⟨k', hk'E, hk', rfl⟩
    · exact has_congr _ _ _ _ _ (has_inp _ _ _ _ (hraw g hg)) (fun x hx => (heq x hx).symm)
    · exact has_congr _ _ _ _ _ (hh k' (Finset.mem_erase.mpr ⟨hk', Finset.mem_product.mpr
        ⟨hk'E, Finset.mem_univ _⟩⟩)) (fun x hx => (heq x hx).symm)
  have key : ∀ e ∈ E, ∀ o : Option Bool,
      Has (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList A gs (kk e o) := by
    intro e he o
    by_cases hio : (e, o) = k0
    · subst hio; exact hk0'
    · exact hh (e, o) (Finset.mem_erase.mpr ⟨hio, Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩⟩)
  have hall : ∀ f ∈ NEED E, Has (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList A gs f := by
    intro f hf
    rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact has_inp _ _ _ _ (hneg i)
    · exact key e he none
    · exact key e he (some true)
    · exact key e he (some false)
  have hL0 : 0 < (RAW E ∪ (Finset.univ : Finset (Fin n)).image ng).toList.length :=
    List.length_pos_of_mem (hraw _ ((mem_RAW E _).mpr (Or.inl rfl)))
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := pack _ A (NEED E) gs hgs hL0 hall
  have hc2 : ((E ×ˢ (Finset.univ : Finset (Option Bool))).erase k0).card = E.card * 3 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_product.mpr ⟨hk0, Finset.mem_univ _⟩), Finset.card_product]
    simp
  have hE1 : 1 ≤ E.card := Finset.card_pos.mpr ⟨_, hk0⟩
  simp only [List.length_nil, zero_add, hc2] at hlen
  have := (hk Finset.univ (3 * E.card - 1)).mp ⟨C, h1, h2, h3, by rw [h4]; omega, h5⟩
  obtain ⟨_, hp⟩ := this
  rw [Finset.card_univ, Fintype.card_fin] at hp
  omega
def c2 (p : Fin n) (α : Bool) (q : Fin n) (β : Bool) (y : Finset (Fin n)) : Bool :=
  (decide (p ∈ y) == α) && (decide (q ∈ y) == β)
theorem cl_kk (E : Finset (Fin n × Fin n)) (u w : Fin n) (huw : (u, w) ∈ E ∨ (w, u) ∈ E)
    (α β : Bool) (hab : ¬(α = true ∧ β = true)) :
    ∃ k : (Fin n × Fin n) × Option Bool, k.1 ∈ E ∧ kk k.1 k.2 = c2 u α w β := by
  rcases huw with h | h
  · cases α <;> cases β
    · exact ⟨((u, w), none), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k1, c2, hu, hw]⟩
    · exact ⟨((u, w), some false), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k3, c2, hu, hw]⟩
    · exact ⟨((u, w), some true), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k2, c2, hu, hw]⟩
    · exact absurd ⟨rfl, rfl⟩ hab
  · cases α <;> cases β
    · exact ⟨((w, u), none), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k1, c2, hu, hw]⟩
    · exact ⟨((w, u), some true), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k2, c2, hu, hw]⟩
    · exact ⟨((w, u), some false), h, by
        funext x; by_cases hu : u ∈ x <;> by_cases hw : w ∈ x <;> simp [kk, k3, c2, hu, hw]⟩
    · exact absurd ⟨rfl, rfl⟩ hab
theorem nec_edge [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (A : Finset (Finset (Fin n))) (hk : KP E A) (e : Fin n × Fin n) (he : e ∈ E) (β : Bool) :
    ∃ x ∈ A, (e.1 ∈ x ↔ β = true) ∧ (e.2 ∈ x ↔ β = false) := by
  by_contra hno
  apply cheap E A hk (e, if β then some true else some false) he (fun _ => false)
    (Or.inl ((mem_RAW E _).mpr (Or.inl rfl)))
  intro x hx
  have h1 : ¬((e.1 ∈ x ↔ β = true) ∧ (e.2 ∈ x ↔ β = false)) := fun h => hno ⟨x, hx, h⟩
  cases β <;> by_cases a1 : e.1 ∈ x <;> by_cases a2 : e.2 ∈ x <;> simp_all [kk, k2, k3]
theorem nec_path [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (A : Finset (Finset (Fin n))) (hk : KP E A) (i j v : Fin n) (hij : i ≠ j)
    (hiv : (i, v) ∈ E ∨ (v, i) ∈ E) (hjv : (j, v) ∈ E ∨ (v, j) ∈ E) (β : Bool) :
    ∃ x ∈ A, (v ∈ x ↔ β = true) ∧ ¬(i ∈ x ↔ j ∈ x) := by
  have hvi : v ≠ i := by
    rintro rfl
    rcases hiv with h | h
    · exact absurd (hE _ h) (lt_irrefl _)
    · exact absurd (hE _ h) (lt_irrefl _)
  obtain ⟨k0, hk0E, hk0⟩ := cl_kk E i v hiv (!β) β (by cases β <;> simp)
  obtain ⟨k1', hk1E, hk1⟩ := cl_kk E j v hjv (!β) β (by cases β <;> simp)
  by_contra hno
  have hne : k1' ≠ k0 := by
    intro h
    rw [h, hk0] at hk1
    have h3 := congrFun hk1 (if β then Finset.univ.erase i else {i})
    cases β
    · simp [c2, hvi, hij, hij.symm] at h3
    · simp [c2, hvi, hij, hij.symm, Finset.mem_erase] at h3
  apply cheap E A hk k0 hk0E (kk k1'.1 k1'.2) (Or.inr ⟨k1', hk1E, hne, rfl⟩)
  intro x hx
  rw [hk0, hk1]
  have h1 : ¬((v ∈ x ↔ β = true) ∧ ¬(i ∈ x ↔ j ∈ x)) := fun h => hno ⟨x, hx, h⟩
  cases β <;> by_cases a1 : i ∈ x <;> by_cases a2 : j ∈ x <;> by_cases a3 : v ∈ x <;> simp_all [c2]
theorem suffK [DecidableEq (Finset (Fin n) → Bool)] (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hconn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ)
    (A : Finset (Finset (Fin n))) (h0 : ∅ ∈ A) (h1 : Finset.univ ∈ A)
    (hD : ∀ f ∈ NEED E, ∀ g ∈ NEED E, f ≠ g → ∃ x ∈ A, f x ≠ g x)
    (hR : ∀ f ∈ NEED E, ∀ g ∈ RAW E, ∃ x ∈ A, f x ≠ g x) : KP E A := by
  intro S p
  have hsurj : Function.Surjective (fun _ : Fin n => (0 : Fin 1)) :=
    fun j => ⟨⟨0, by omega⟩, Subsingleton.elim _ _⟩
  have hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, (fun _ : Fin n => (0 : Fin 1)) i = (fun _ : Fin n => (0 : Fin 1)) j → (i ∈ Z ↔ j ∈ Z) := by
    intro Z
    constructor
    · intro h i j _
      rcases hconn Z h with rfl | rfl <;> simp
    · intro h e _
      exact h e.1 e.2 rfl
  have hF : ∀ κ : Fin 1, ∃ y ∈ A, (∀ v ∈ y, (fun _ : Fin n => (0 : Fin 1)) v ≠ κ) ∧
      y ∪ Finset.univ.filter (fun v => (fun _ : Fin n => (0 : Fin 1)) v = κ) ∈ A := by
    intro κ
    refine ⟨∅, h0, by simp, ?_⟩
    have hk : κ = 0 := Subsingleton.elim _ _
    subst hk
    simpa using h1
  refine (suff E (fun _ => (0 : Fin 1)) hE hsurj hcomp A hF hD hR S p).trans ?_
  constructor
  · rintro ⟨hc, hp⟩
    obtain ⟨i, hi, _⟩ := hc 0
    exact ⟨⟨i, hi⟩, hp⟩
  · rintro ⟨⟨i, hi⟩, hp⟩
    exact ⟨fun j => ⟨i, hi, Subsingleton.elim _ _⟩, hp⟩
end Nec2
section Count
variable {n : ℕ}
def Hs (n : ℕ) : Finset (Finset (Fin n)) := Finset.powersetCard (n / 2) Finset.univ
abbrev Ix (n a D : ℕ) := (Fin D × Bool) ⊕ (Fin a × ↥(Hs n) × Bool)
def rho (n a D : ℕ) : Ix n a D → Finset (Fin n)
  | Sum.inl (_, β) => if β then Finset.univ else ∅
  | Sum.inr (_, y, β) => if β then Finset.univ \ y.1 else y.1
def cnt (n a D : ℕ) (p : Finset (Fin n) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Ix n a D => p (rho n a D i) = true)).card
def c3 (u : Fin n) (α : Bool) (v : Fin n) (β : Bool) (w : Fin n) (γ : Bool) (y : Finset (Fin n)) : Bool :=
  (decide (u ∈ y) == α) && (decide (v ∈ y) == β) && (decide (w ∈ y) == γ)
theorem cnt_mono (a D : ℕ) (p q : Finset (Fin n) → Bool) (h : ∀ y, p y = true → q y = true) :
    cnt n a D p ≤ cnt n a D q := by
  unfold cnt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h _ hi
theorem cnt_add (a D : ℕ) (p q r : Finset (Fin n) → Bool) (hd : ∀ y, ¬(p y = true ∧ q y = true))
    (hp : ∀ y, p y = true → r y = true) (hq : ∀ y, q y = true → r y = true) :
    cnt n a D p + cnt n a D q ≤ cnt n a D r := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with h | h
    · exact hp _ h
    · exact hq _ h
  · rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hd _ ⟨h1, h2⟩
theorem cnt_eq (a D : ℕ) (p : Finset (Fin n) → Bool) :
    cnt n a D p = D * ((if p Finset.univ = true then 1 else 0) + (if p ∅ = true then 1 else 0)) +
      a * (((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card +
        ((Hs n).filter (fun y => p y = true)).card) := by
  unfold cnt
  rw [Finset.card_filter, Fintype.sum_sum_type, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_coe_sort (Hs n)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, rho, ↓reduceIte, Bool.false_eq_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
theorem card_ix (a D : ℕ) : Fintype.card (Ix n a D) = 2 * D + 2 * (a * Nat.choose n (n / 2)) := by
  simp [Ix, Hs, Fintype.card_sum, Fintype.card_prod, Finset.card_powersetCard]
  ring
theorem cnt_U0 (a D : ℕ) (p : Finset (Fin n) → Bool) (hp : p ∅ = true) : D ≤ cnt n a D p := by
  rw [cnt_eq, hp]
  simp only [↓reduceIte]
  generalize (if p Finset.univ = true then 1 else 0) = x
  generalize a * (((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card +
        ((Hs n).filter (fun y => p y = true)).card) = z
  nlinarith
theorem cnt_U1 (a D : ℕ) (p : Finset (Fin n) → Bool) (hp : p Finset.univ = true) : D ≤ cnt n a D p := by
  rw [cnt_eq, hp]
  simp only [↓reduceIte]
  generalize (if p ∅ = true then 1 else 0) = x
  generalize a * (((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card +
        ((Hs n).filter (fun y => p y = true)).card) = z
  nlinarith
theorem cnt_NU (a D : ℕ) (p : Finset (Fin n) → Bool) :
    a * ((Hs n).filter (fun y => p y = true)).card +
      a * ((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card ≤ cnt n a D p := by
  rw [cnt_eq, Nat.mul_add a]
  omega
theorem ic (I O : Finset (Fin n)) (hIO : Disjoint I O) (m : ℕ) (hm : m + I.card = n / 2) :
    Nat.choose (n - I.card - O.card) m ≤ ((Hs n).filter (fun y => I ⊆ y ∧ Disjoint O y)).card := by
  have hc : (Finset.univ \ (I ∪ O)).card = n - I.card - O.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_union_of_disjoint hIO,
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hc, ← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun z => z ∪ I)
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hz
    simp only [Finset.mem_coe, Finset.mem_filter, Hs, Finset.mem_powersetCard]
    have hzI : Disjoint z I := by
      rw [Finset.disjoint_left]
      intro v hv hvI
      have h5 := hz.1 hv
      simp [hvI] at h5
    refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_union_of_disjoint hzI, hz.2, hm]⟩,
      Finset.subset_union_right, ?_⟩
    rw [Finset.disjoint_left]
    intro v hvO hv
    rcases Finset.mem_union.mp hv with h | h
    · have h5 := hz.1 h
      simp [hvO] at h5
    · exact Finset.disjoint_left.mp hIO h hvO
  · intro z hz z' hz' he
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hz hz'
    have h1 : ∀ v, v ∈ z → v ∉ I := fun v hv hvI => by
      have h5 := hz.1 hv
      simp [hvI] at h5
    have h2 : ∀ v, v ∈ z' → v ∉ I := fun v hv hvI => by
      have h5 := hz'.1 hv
      simp [hvI] at h5
    ext v
    have h3 : v ∈ z ∪ I ↔ v ∈ z' ∪ I := by
      have h4 : z ∪ I = z' ∪ I := he
      rw [h4]
    simp only [Finset.mem_union] at h3
    constructor
    · intro hv
      rcases h3.mp (Or.inl hv) with h | h
      · exact h
      · exact absurd h (h1 v hv)
    · intro hv
      rcases h3.mpr (Or.inl hv) with h | h
      · exact h
      · exact absurd h (h2 v hv)
theorem ic1 (u w : Fin n) (huw : u ≠ w) (hh : 1 ≤ n / 2) :
    Nat.choose (n - 2) (n / 2 - 1) ≤ ((Hs n).filter (fun y => u ∈ y ∧ w ∉ y)).card := by
  have h := ic {u} {w} (Finset.disjoint_singleton.mpr huw) (n / 2 - 1)
    (by rw [Finset.card_singleton]; omega)
  rw [Finset.card_singleton, Finset.card_singleton, show n - 1 - 1 = n - 2 by omega] at h
  refine le_trans h (Finset.card_le_card ?_)
  intro y hy
  simp only [Finset.mem_filter, Finset.singleton_subset_iff, Finset.disjoint_singleton_left] at hy ⊢
  exact hy
theorem ic2 (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hh : 1 ≤ n / 2) :
    Nat.choose (n - 3) (n / 2 - 1) ≤ ((Hs n).filter (fun y => u ∈ y ∧ v ∉ y ∧ w ∉ y)).card := by
  have hd : Disjoint ({u} : Finset (Fin n)) {v, w} := by simp [huv, huw]
  have h := ic {u} {v, w} hd (n / 2 - 1) (by rw [Finset.card_singleton]; omega)
  rw [Finset.card_singleton, Finset.card_pair hvw, show n - 1 - 2 = n - 3 by omega] at h
  refine le_trans h (Finset.card_le_card ?_)
  intro y hy
  simp only [Finset.mem_filter, Finset.singleton_subset_iff] at hy ⊢
  refine ⟨hy.1, hy.2.1, ?_, ?_⟩
  · exact Finset.disjoint_left.mp hy.2.2 (by simp)
  · exact Finset.disjoint_left.mp hy.2.2 (by simp)
theorem ic3 (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hh : 2 ≤ n / 2) :
    Nat.choose (n - 3) (n / 2 - 2) ≤ ((Hs n).filter (fun y => u ∉ y ∧ v ∈ y ∧ w ∈ y)).card := by
  have hd : Disjoint ({v, w} : Finset (Fin n)) {u} := by simp [huv, huw, huv.symm, huw.symm]
  have h := ic {v, w} {u} hd (n / 2 - 2) (by rw [Finset.card_pair hvw]; omega)
  rw [Finset.card_singleton, Finset.card_pair hvw, show n - 2 - 1 = n - 3 by omega] at h
  refine le_trans h (Finset.card_le_card ?_)
  intro y hy
  simp only [Finset.mem_filter, Finset.disjoint_singleton_left] at hy ⊢
  refine ⟨hy.1, hy.2.2, hy.2.1 (by simp), hy.2.1 (by simp)⟩
theorem k3num (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Nat.choose (n - 2) (n / 2 - 1) ≤ ((Hs n).filter (fun y => u ∈ y ∧ v ∉ y ∧ w ∉ y)).card +
      ((Hs n).filter (fun y => u ∉ y ∧ v ∈ y ∧ w ∈ y)).card := by
  have hn3 : 3 ≤ n := by
    have h1 : ({u, v, w} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [huv, huw]), Finset.card_pair hvw]
    have h2 := Finset.card_le_univ ({u, v, w} : Finset (Fin n))
    simp only [Fintype.card_fin] at h2
    omega
  have hh : 1 ≤ n / 2 := by omega
  have a1 := ic2 u v w huv huw hvw hh
  rcases Nat.lt_or_ge (n / 2) 2 with h2 | h2
  · have e : n / 2 - 1 = 0 := by omega
    rw [e, Nat.choose_zero_right] at a1 ⊢
    omega
  · have a2 := ic3 u v w huv huw hvw h2
    have e : Nat.choose (n - 2) (n / 2 - 1) =
        Nat.choose (n - 3) (n / 2 - 2) + Nat.choose (n - 3) (n / 2 - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, n - 3 = m := ⟨_, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j, n / 2 - 2 = j := ⟨_, rfl⟩
      rw [show n - 2 = m + 1 by omega, show n / 2 - 1 = j + 1 by omega, hm, hj, Nat.choose_succ_succ']
    omega
theorem K2 (a D : ℕ) (hD : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) (hn : 2 ≤ n) (u w : Fin n)
    (huw : u ≠ w) (α β : Bool) :
    2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (c2 u α w β) := by
  have hh : 1 ≤ n / 2 := by omega
  have h1 := ic1 w u huw.symm hh
  have h2 := ic1 u w huw hh
  have h3 := cnt_NU a D (c2 u α w β)
  cases α <;> cases β
  · exact le_trans hD (cnt_U0 a D _ (by simp [c2]))
  · have m1 : ((Hs n).filter (fun y => w ∈ y ∧ u ∉ y)).card ≤
        ((Hs n).filter (fun y => c2 u false w true y = true)).card :=
      Finset.card_le_card (fun y hy => by
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by simp [c2, hy.2.1, hy.2.2]⟩)
    have m2 : ((Hs n).filter (fun y => u ∈ y ∧ w ∉ y)).card ≤
        ((Hs n).filter (fun y => c2 u false w true (Finset.univ \ y) = true)).card :=
      Finset.card_le_card (fun y hy => by
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by simp [c2, hy.2.1, hy.2.2]⟩)
    have q1 := Nat.mul_le_mul_left a (h1.trans m1)
    have q2 := Nat.mul_le_mul_left a (h2.trans m2)
    nlinarith
  · have m1 : ((Hs n).filter (fun y => u ∈ y ∧ w ∉ y)).card ≤
        ((Hs n).filter (fun y => c2 u true w false y = true)).card :=
      Finset.card_le_card (fun y hy => by
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by simp [c2, hy.2.1, hy.2.2]⟩)
    have m2 : ((Hs n).filter (fun y => w ∈ y ∧ u ∉ y)).card ≤
        ((Hs n).filter (fun y => c2 u true w false (Finset.univ \ y) = true)).card :=
      Finset.card_le_card (fun y hy => by
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by simp [c2, hy.2.1, hy.2.2]⟩)
    have q1 := Nat.mul_le_mul_left a (h2.trans m1)
    have q2 := Nat.mul_le_mul_left a (h1.trans m2)
    nlinarith
  · exact le_trans hD (cnt_U1 a D _ (by simp [c2]))
theorem K3odd (a D : ℕ) (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (p : Finset (Fin n) → Bool)
    (h1 : ∀ y, u ∈ y → v ∉ y → w ∉ y → p y = true)
    (h2 : ∀ y, u ∉ y → v ∈ y → w ∈ y → p (Finset.univ \ y) = true) :
    a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D p := by
  have h3 := cnt_NU a D p
  have hk := k3num u v w huv huw hvw
  have m1 : ((Hs n).filter (fun y => u ∈ y ∧ v ∉ y ∧ w ∉ y)).card ≤
      ((Hs n).filter (fun y => p y = true)).card :=
    Finset.card_le_card (fun y hy => by
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, h1 y hy.2.1 hy.2.2.1 hy.2.2.2⟩)
  have m2 : ((Hs n).filter (fun y => u ∉ y ∧ v ∈ y ∧ w ∈ y)).card ≤
      ((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card :=
    Finset.card_le_card (fun y hy => by
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, h2 y hy.2.1 hy.2.2.1 hy.2.2.2⟩)
  have q := Nat.mul_le_mul_left a (le_trans hk (Nat.add_le_add m1 m2))
  rw [Nat.mul_add] at q
  omega
theorem K3odd' (a D : ℕ) (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (p : Finset (Fin n) → Bool)
    (h1 : ∀ y, u ∈ y → v ∉ y → w ∉ y → p (Finset.univ \ y) = true)
    (h2 : ∀ y, u ∉ y → v ∈ y → w ∈ y → p y = true) :
    a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D p := by
  have h3 := cnt_NU a D p
  have hk := k3num u v w huv huw hvw
  have m1 : ((Hs n).filter (fun y => u ∈ y ∧ v ∉ y ∧ w ∉ y)).card ≤
      ((Hs n).filter (fun y => p (Finset.univ \ y) = true)).card :=
    Finset.card_le_card (fun y hy => by
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, h1 y hy.2.1 hy.2.2.1 hy.2.2.2⟩)
  have m2 : ((Hs n).filter (fun y => u ∉ y ∧ v ∈ y ∧ w ∈ y)).card ≤
      ((Hs n).filter (fun y => p y = true)).card :=
    Finset.card_le_card (fun y hy => by
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, h2 y hy.2.1 hy.2.2.1 hy.2.2.2⟩)
  have q := Nat.mul_le_mul_left a (le_trans hk (Nat.add_le_add m1 m2))
  rw [Nat.mul_add] at q
  omega
theorem K3 (a D : ℕ) (hD : a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) (u v w : Fin n) (huv : u ≠ v)
    (huw : u ≠ w) (hvw : v ≠ w) (α β γ : Bool) :
    a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (c3 u α v β w γ) := by
  cases α <;> cases β <;> cases γ
  · exact le_trans hD (cnt_U0 a D _ (by simp [c3]))
  · exact K3odd a D w u v huw.symm hvw.symm huv _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact K3odd a D v u w huv.symm hvw huw _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact K3odd' a D u v w huv huw hvw _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact K3odd a D u v w huv huw hvw _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact K3odd' a D v u w huv.symm hvw huw _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact K3odd' a D w u v huw.symm hvw.symm huv _
      (fun y h1 h2 h3 => by simp [c3, h1, h2, h3]) (fun y h1 h2 h3 => by simp [c3, h1, h2, h3])
  · exact le_trans hD (cnt_U1 a D _ (by simp [c3]))
theorem bl_sep1 : ∀ b1 b2 β : Bool, ((b1 == β) && (b2 == !β)) = true →
    ((b1 != b2) && (b1 == β)) = true := by decide
theorem bl_sep2 : ∀ b1 b2 β : Bool, ((b1 == !β) && (b2 == β)) = true →
    ((b1 != b2) && (b2 == β)) = true := by decide
theorem bl_sep3 : ∀ b1 b2 b3 β : Bool, ((b1 == true) && (b2 == false) && (b3 == β)) = true →
    ((b1 != b2) && (b3 == β)) = true := by decide
theorem bl_sep4 : ∀ b1 b2 b3 β : Bool, ((b1 == false) && (b2 == true) && (b3 == β)) = true →
    ((b1 != b2) && (b3 == β)) = true := by decide
theorem Ksep (a D : ℕ) (hD : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) (hn : 2 ≤ n)
    (s t p : Fin n) (hst : s ≠ t) (β : Bool) :
    2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤
      cnt n a D (fun y => (decide (s ∈ y) != decide (t ∈ y)) && (decide (p ∈ y) == β)) := by
  by_cases hps : p = s
  · subst hps
    exact le_trans (K2 a D hD hn p t hst β (!β)) (cnt_mono a D _ _ (fun y hy => bl_sep1 _ _ _ hy))
  by_cases hpt : p = t
  · subst hpt
    exact le_trans (K2 a D hD hn s p hst (!β) β) (cnt_mono a D _ _ (fun y hy => bl_sep2 _ _ _ hy))
  have hD3 : a * Nat.choose (n - 2) (n / 2 - 1) ≤ D := le_trans (by nlinarith) hD
  have X := K3 a D hD3 s t p hst (Ne.symm hps) (Ne.symm hpt) true false β
  have Y := K3 a D hD3 s t p hst (Ne.symm hps) (Ne.symm hpt) false true β
  have Z := cnt_add a D (c3 s true t false p β) (c3 s false t true p β)
    (fun y => (decide (s ∈ y) != decide (t ∈ y)) && (decide (p ∈ y) == β))
    (fun y h => by
      obtain ⟨h1, h2⟩ := h
      simp only [c3, Bool.and_eq_true, beq_iff_eq] at h1 h2
      rw [h1.1.1] at h2
      exact absurd h2.1.1 (by decide))
    (fun y hy => bl_sep3 _ _ _ _ hy) (fun y hy => bl_sep4 _ _ _ _ hy)
  have e2 : 2 * a * Nat.choose (n - 2) (n / 2 - 1) =
      a * Nat.choose (n - 2) (n / 2 - 1) + a * Nat.choose (n - 2) (n / 2 - 1) := by ring
  omega
theorem lit (p q s t : Fin n) (α β γ δ : Bool) (hst : s ≠ t) (hne : c2 p α q β ≠ c2 s γ t δ) :
    ∃ s' γ', (s' = s ∧ γ' = γ ∨ s' = t ∧ γ' = δ) ∧ ¬(s' = p ∧ γ' = α) ∧ ¬(s' = q ∧ γ' = β) := by
  by_cases c1 : (s = p ∧ γ = α) ∨ (s = q ∧ γ = β)
  · by_cases c2' : (t = p ∧ δ = α) ∨ (t = q ∧ δ = β)
    · exfalso
      apply hne
      rcases c1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases c2' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact absurd (h1.trans h3.symm) hst
      · rw [h1, h2, h3, h4]
      · rw [h1, h2, h3, h4]
        funext y
        exact Bool.and_comm _ _
      · exact absurd (h1.trans h3.symm) hst
    · exact ⟨t, δ, Or.inr ⟨rfl, rfl⟩, fun h => c2' (Or.inl h), fun h => c2' (Or.inr h)⟩
  · exact ⟨s, γ, Or.inl ⟨rfl, rfl⟩, fun h => c1 (Or.inl h), fun h => c1 (Or.inr h)⟩
theorem bl1 : ∀ b1 b2 γ δ : Bool, (b1 == !γ) = true → ((b1 == γ) && (b2 == δ)) = false := by decide
theorem bl2 : ∀ b1 b2 γ δ : Bool, (b2 == !δ) = true → ((b1 == γ) && (b2 == δ)) = false := by decide
theorem bl3 : ∀ b1 b2 α β γ' : Bool, γ' ≠ α → ((b1 == α) && (b2 == β)) = true → (b1 == !γ') = true := by
  decide
theorem bl4 : ∀ b1 b2 α β γ' : Bool, γ' ≠ β → ((b1 == α) && (b2 == β)) = true → (b2 == !γ') = true := by
  decide
theorem lit_off (p q s t : Fin n) (α β γ δ : Bool) (s' : Fin n) (γ' : Bool)
    (hs' : s' = s ∧ γ' = γ ∨ s' = t ∧ γ' = δ) (y : Finset (Fin n))
    (hy : (decide (s' ∈ y) == !γ') = true) : c2 s γ t δ y = false := by
  rcases hs' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hy
    exact bl1 _ _ _ _ hy
  · rw [h1, h2] at hy
    exact bl2 _ _ _ _ hy
theorem CC (a D : ℕ) (hD : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) (hn : 2 ≤ n)
    (p q s t : Fin n) (hpq : p ≠ q) (hst : s ≠ t) (α β γ δ : Bool) (hne : c2 p α q β ≠ c2 s γ t δ) :
    2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => c2 p α q β y != c2 s γ t δ y) := by
  obtain ⟨s', γ', hs', hn1, hn2⟩ := lit p q s t α β γ δ hst hne
  obtain ⟨p', α', hp', hm1, hm2⟩ := lit s t p q γ δ α β hpq (Ne.symm hne)
  have G := lit_off p q s t α β γ δ s' γ' hs'
  have F := lit_off s t p q γ δ α β p' α' hp'
  by_cases e1 : s' = p
  · have hγ : γ' ≠ α := fun h => hn1 ⟨e1, h⟩
    refine le_trans (K2 a D hD hn p q hpq α β) (cnt_mono a D _ _ ?_)
    intro y hy
    have h5 : (decide (s' ∈ y) == !γ') = true := by rw [e1]; exact bl3 _ _ _ _ _ hγ hy
    rw [G y h5, hy]
    rfl
  by_cases e2 : s' = q
  · have hγ : γ' ≠ β := fun h => hn2 ⟨e2, h⟩
    refine le_trans (K2 a D hD hn p q hpq α β) (cnt_mono a D _ _ ?_)
    intro y hy
    have h5 : (decide (s' ∈ y) == !γ') = true := by rw [e2]; exact bl4 _ _ _ _ _ hγ hy
    rw [G y h5, hy]
    rfl
  by_cases e3 : p' = s
  · have hα : α' ≠ γ := fun h => hm1 ⟨e3, h⟩
    refine le_trans (K2 a D hD hn s t hst γ δ) (cnt_mono a D _ _ ?_)
    intro y hy
    have h5 : (decide (p' ∈ y) == !α') = true := by rw [e3]; exact bl3 _ _ _ _ _ hα hy
    rw [F y h5, hy]
    rfl
  by_cases e4 : p' = t
  · have hα : α' ≠ δ := fun h => hm2 ⟨e4, h⟩
    refine le_trans (K2 a D hD hn s t hst γ δ) (cnt_mono a D _ _ ?_)
    intro y hy
    have h5 : (decide (p' ∈ y) == !α') = true := by rw [e4]; exact bl4 _ _ _ _ _ hα hy
    rw [F y h5, hy]
    rfl
  have hD3 : a * Nat.choose (n - 2) (n / 2 - 1) ≤ D := le_trans (by nlinarith) hD
  have X := K3 a D hD3 p q s' hpq (fun h => e1 h.symm) (fun h => e2 h.symm) α β (!γ')
  have Y := K3 a D hD3 s t p' hst (fun h => e3 h.symm) (fun h => e4 h.symm) γ δ (!α')
  have Z := cnt_add a D (c3 p α q β s' (!γ')) (c3 s γ t δ p' (!α'))
    (fun y => c2 p α q β y != c2 s γ t δ y)
    (fun y h => by
      obtain ⟨h1, h2⟩ := h
      have g1 : c2 s γ t δ y = false := G y (by
        simp only [c3, Bool.and_eq_true] at h1
        exact h1.2)
      have g2 : c2 s γ t δ y = true := by
        simp only [c3, Bool.and_eq_true] at h2
        simp only [c2, Bool.and_eq_true]
        exact h2.1
      rw [g1] at g2
      exact absurd g2 (by decide))
    (fun y h => by
      have g1 : c2 s γ t δ y = false := G y (by
        simp only [c3, Bool.and_eq_true] at h
        exact h.2)
      have g2 : c2 p α q β y = true := by
        simp only [c3, Bool.and_eq_true] at h
        simp only [c2, Bool.and_eq_true]
        exact h.1
      rw [g1, g2]
      rfl)
    (fun y h => by
      have g1 : c2 p α q β y = false := F y (by
        simp only [c3, Bool.and_eq_true] at h
        exact h.2)
      have g2 : c2 s γ t δ y = true := by
        simp only [c3, Bool.and_eq_true] at h
        simp only [c2, Bool.and_eq_true]
        exact h.1
      rw [g1, g2]
      rfl)
  have e2 : 2 * a * Nat.choose (n - 2) (n / 2 - 1) =
      a * Nat.choose (n - 2) (n / 2 - 1) + a * Nat.choose (n - 2) (n / 2 - 1) := by ring
  omega
end Count
section Pairs
variable {n : ℕ}
theorem r_k1 (e : Fin n × Fin n) : k1 e = c2 e.1 false e.2 false := by
  funext y; simp [k1, c2]
theorem r_k2 (e : Fin n × Fin n) : k2 e = c2 e.1 true e.2 false := by
  funext y; simp [k2, c2]
theorem r_k3 (e : Fin n × Fin n) : k3 e = c2 e.1 false e.2 true := by
  funext y; simp [k3, c2]
theorem bl_comm : ∀ b1 b2 : Bool, ((b1 != b2) = true ↔ (b2 != b1) = true) := by decide
theorem cnt_sym (a D : ℕ) (f g : Finset (Fin n) → Bool) :
    cnt n a D (fun y => f y != g y) = cnt n a D (fun y => g y != f y) := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro i _
  exact bl_comm _ _
theorem bk2 : ∀ b1 b2 : Bool, ((b1 == true) && (b2 == false)) = true → ((b1 && !b2) != false) = true := by
  decide
theorem bk3 : ∀ b1 b2 : Bool, ((b1 == false) && (b2 == true)) = true → ((!b1 && b2) != false) = true := by
  decide
theorem bkn2 : ∀ b1 b2 c1 c2 : Bool, ((c1 != c2) && (b1 == false)) = true →
    ((b1 && !b2) != !(c1 == c2)) = true := by decide
theorem bkn3 : ∀ b1 b2 c1 c2 : Bool, ((c1 != c2) && (b1 == true)) = true →
    ((!b1 && b2) != !(c1 == c2)) = true := by decide
theorem bnk1 : ∀ bi b2 : Bool, ((b2 == true) && (bi == false)) = true → ((!bi) != (!bi && !b2)) = true := by
  decide
theorem bnk2 : ∀ b1 b2 bi : Bool, ((b1 == true) && (bi == false)) = true → ((!bi) != (!b1 && !b2)) = true := by
  decide
theorem bnn : ∀ b1 b2 : Bool, ((b1 == true) && (b2 == false)) = true → ((!b1) != (!b2)) = true := by
  decide
theorem pairsR [DecidableEq (Finset (Fin n) → Bool)] (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2) (a D : ℕ) (hD : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) :
    ∀ f ∈ NEED E, ∀ g ∈ RAW E, 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => f y != g y) := by
  have U0 : ∀ f g : Finset (Fin n) → Bool, f ∅ ≠ g ∅ →
      2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => f y != g y) :=
    fun f g h => le_trans hD (cnt_U0 a D _ (by simpa using h))
  have U1 : ∀ f g : Finset (Fin n) → Bool, f Finset.univ ≠ g Finset.univ →
      2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => f y != g y) :=
    fun f g h => le_trans hD (cnt_U1 a D _ (by simpa using h))
  intro f hf g hg
  rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;>
  rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨j, rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
  · exact U0 _ _ (by simp [ng])
  · exact U1 _ _ (by simp [ng])
  · exact U0 _ _ (by simp [ng, bt])
  · exact U1 _ _ (by simp [ng, sm])
  · exact U0 _ _ (by simp [ng, ns])
  · exact U0 _ _ (by simp [k1])
  · exact U1 _ _ (by simp [k1])
  · exact U0 _ _ (by simp [k1, bt])
  · exact U1 _ _ (by simp [k1, sm])
  · exact U0 _ _ (by simp [k1, ns])
  · exact le_trans (K2 a D hD hn e.1 e.2 (ne_of_lt (hE e he)) true false)
      (cnt_mono a D _ _ (fun y hy => bk2 _ _ hy))
  · exact U1 _ _ (by simp [k2])
  · exact U1 _ _ (by simp [k2, bt])
  · exact U1 _ _ (by simp [k2, sm])
  · exact le_trans (Ksep a D hD hn e'.1 e'.2 e.1 (ne_of_lt (hE e' he')) false)
      (cnt_mono a D _ _ (fun y hy => bkn2 _ _ _ _ hy))
  · exact le_trans (K2 a D hD hn e.1 e.2 (ne_of_lt (hE e he)) false true)
      (cnt_mono a D _ _ (fun y hy => bk3 _ _ hy))
  · exact U1 _ _ (by simp [k3])
  · exact U1 _ _ (by simp [k3, bt])
  · exact U1 _ _ (by simp [k3, sm])
  · exact le_trans (Ksep a D hD hn e'.1 e'.2 e.1 (ne_of_lt (hE e' he')) true)
      (cnt_mono a D _ _ (fun y hy => bkn3 _ _ _ _ hy))
theorem pairsD [DecidableEq (Finset (Fin n) → Bool)] (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2) (a D : ℕ) (hD : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D) :
    ∀ f ∈ NEED E, ∀ g ∈ NEED E, f ≠ g →
      2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => f y != g y) := by
  have U0 : ∀ f g : Finset (Fin n) → Bool, f ∅ ≠ g ∅ →
      2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ cnt n a D (fun y => f y != g y) :=
    fun f g h => le_trans hD (cnt_U0 a D _ (by simpa using h))
  have hNK : ∀ i, ∀ e ∈ E, 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤
      cnt n a D (fun y => ng i y != k1 e y) := by
    intro i e he
    by_cases h1 : e.1 = i
    · have h2 : e.2 ≠ i := by rw [← h1]; exact (ne_of_lt (hE e he)).symm
      refine le_trans (K2 a D hD hn e.2 i h2 true false) (cnt_mono a D _ _ (fun y hy => ?_))
      have h3 : k1 e y = (!decide (i ∈ y) && !decide (e.2 ∈ y)) := by simp only [k1, h1]
      rw [h3]
      exact bnk1 _ _ hy
    · exact le_trans (K2 a D hD hn e.1 i h1 true false)
        (cnt_mono a D _ _ (fun y hy => bnk2 _ _ _ hy))
  intro f hf g hg hfg
  rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;>
  rcases (mem_NEED E g).mp hg with ⟨j, rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
  · have hij : i ≠ j := fun h => hfg (h ▸ rfl)
    exact le_trans (K2 a D hD hn i j hij true false) (cnt_mono a D _ _ (fun y hy => bnn _ _ hy))
  · exact hNK i e' he'
  · exact U0 _ _ (by simp [ng, k2])
  · exact U0 _ _ (by simp [ng, k3])
  · rw [cnt_sym]; exact hNK j e he
  · rw [r_k1 e, r_k1 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k1 e, r_k2 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k1 e, r_k3 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · exact U0 _ _ (by simp [ng, k2])
  · rw [r_k2 e, r_k1 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k2 e, r_k2 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k2 e, r_k3 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · exact U0 _ _ (by simp [ng, k3])
  · rw [r_k3 e, r_k1 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k3 e, r_k2 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
  · rw [r_k3 e, r_k3 e'] at hfg ⊢
    exact CC a D hD hn _ _ _ _ (ne_of_lt (hE e he)) (ne_of_lt (hE e' he')) _ _ _ _ hfg
end Pairs
section Final
variable {n : ℕ}
theorem upper [DecidableEq (Finset (Fin n) → Bool)] {dW : DecidableEq (Finset (Fin n))}
    {dk : ∀ k, DecidableEq (Fin k)} (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hconn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ)
    (a : ℕ) (ha : 0 < a) :
    ∃ k : ℕ, k = 2 * (2 * a * Nat.choose (n - 2) (n / 2 - 1)) + 2 * (a * Nat.choose n (n / 2)) ∧
      ∃ rows : Fin k → Finset (Fin n), ∀ erased : Finset (Fin k),
        erased.card ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) - 1 →
          KP E ((Finset.univ \ erased).image rows) := by
  have hC : 0 < Nat.choose (n - 2) (n / 2 - 1) := Nat.choose_pos (by omega)
  have hD1 : 1 ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) ha) hC
  generalize hDd : 2 * a * Nat.choose (n - 2) (n / 2 - 1) = D at hD1 ⊢
  have hDle : 2 * a * Nat.choose (n - 2) (n / 2 - 1) ≤ D := hDd.le
  refine ⟨Fintype.card (Ix n a D), card_ix a D,
    fun t => rho n a D ((Fintype.equivFin (Ix n a D)).symm t), fun erased herased => ?_⟩
  have ex : ∀ p : Finset (Fin n) → Bool, D ≤ cnt n a D p →
      ∃ x ∈ (Finset.univ \ erased).image (fun t => rho n a D ((Fintype.equivFin (Ix n a D)).symm t)),
        p x = true := by
    intro p hp
    by_contra H
    have hsub : Finset.univ.filter
        (fun t => p (rho n a D ((Fintype.equivFin (Ix n a D)).symm t)) = true) ⊆ erased := by
      intro t ht
      by_contra hte
      exact H ⟨_, Finset.mem_image.mpr ⟨t, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hte⟩, rfl⟩,
        (Finset.mem_filter.mp ht).2⟩
    have hc : (Finset.univ.filter
        (fun t => p (rho n a D ((Fintype.equivFin (Ix n a D)).symm t)) = true)).card = cnt n a D p := by
      unfold cnt
      symm
      apply Finset.card_equiv (Fintype.equivFin (Ix n a D))
      intro i
      simp
    have h6 := Finset.card_le_card hsub
    omega
  have hDp := pairsD hn E hE a D hDle
  have hRp := pairsR hn E hE a D hDle
  apply suffK hn E hE hconn
  · obtain ⟨x, hx, hpx⟩ := ex (fun y => decide (y = ∅)) (cnt_U0 a D _ (by simp))
    have h7 : x = ∅ := by simpa using hpx
    rw [h7] at hx
    exact hx
  · obtain ⟨x, hx, hpx⟩ := ex (fun y => decide (y = Finset.univ)) (cnt_U1 a D _ (by simp))
    have h7 : x = Finset.univ := by simpa using hpx
    rw [h7] at hx
    exact hx
  · intro f hf g hg hfg
    obtain ⟨x, hx, hpx⟩ := ex _ (le_trans hDd.ge (hDp f hf g hg hfg))
    exact ⟨x, hx, by simpa using hpx⟩
  · intro f hf g hg
    obtain ⟨x, hx, hpx⟩ := ex _ (le_trans hDd.ge (hRp f hf g hg))
    exact ⟨x, hx, by simpa using hpx⟩
theorem cnt_rob {k : ℕ} {dk : DecidableEq (Fin k)} {dW : DecidableEq (Finset (Fin n))}
    (rows : Fin k → Finset (Fin n)) (d : ℕ) (Q : Finset (Finset (Fin n)) → Prop)
    (hrob : ∀ erased : Finset (Fin k), erased.card ≤ d → Q ((Finset.univ \ erased).image rows))
    (P : Finset (Fin n) → Prop) [DecidablePred P] (hQ : ∀ A, Q A → ∃ x ∈ A, P x) :
    d < (Finset.univ.filter (fun t => P (rows t))).card := by
  by_contra H
  obtain ⟨x, hx, hP⟩ := hQ _ (hrob (Finset.univ.filter (fun t => P (rows t))) (by omega))
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)
theorem sep2 {k : ℕ} {dk : DecidableEq (Fin k)} {dW : DecidableEq (Finset (Fin n))}
    (E : Finset (Fin n × Fin n))
    (hdiam : ∀ i j : Fin n, i ≠ j → ((i, j) ∈ E ∨ (j, i) ∈ E) ∨
      ∃ v, ((i, v) ∈ E ∨ (v, i) ∈ E) ∧ ((v, j) ∈ E ∨ (j, v) ∈ E))
    (Q : Finset (Finset (Fin n)) → Prop)
    (hQ2 : ∀ A, Q A → ∀ e ∈ E, ∀ β : Bool, ∃ x ∈ A, (e.1 ∈ x ↔ β = true) ∧ (e.2 ∈ x ↔ β = false))
    (hQ3 : ∀ A, Q A → ∀ i j v : Fin n, i ≠ j → ((i, v) ∈ E ∨ (v, i) ∈ E) →
      ((j, v) ∈ E ∨ (v, j) ∈ E) → ∀ β : Bool, ∃ x ∈ A, (v ∈ x ↔ β = true) ∧ ¬(i ∈ x ↔ j ∈ x))
    (D : ℕ) (rows : Fin k → Finset (Fin n))
    (hrob : ∀ erased : Finset (Fin k), erased.card ≤ D - 1 → Q ((Finset.univ \ erased).image rows))
    (hD1 : 1 ≤ D) (i j : Fin n) (hij : i ≠ j) :
    2 * D ≤ (Finset.univ.filter (fun t => ¬(i ∈ rows t ↔ j ∈ rows t))).card := by
  have two : ∀ (P1 P2 : Finset (Fin n) → Prop) [DecidablePred P1] [DecidablePred P2],
      (∀ y, P1 y → ¬ P2 y) → (∀ y, P1 y → ¬(i ∈ y ↔ j ∈ y)) → (∀ y, P2 y → ¬(i ∈ y ↔ j ∈ y)) →
      (∀ A, Q A → ∃ x ∈ A, P1 x) → (∀ A, Q A → ∃ x ∈ A, P2 x) →
      2 * D ≤ (Finset.univ.filter (fun t => ¬(i ∈ rows t ↔ j ∈ rows t))).card := by
    intro P1 P2 _ _ hdis h1 h2 q1 q2
    have c1 := cnt_rob rows (D - 1) Q hrob P1 q1
    have c2' := cnt_rob rows (D - 1) Q hrob P2 q2
    have hd : Disjoint (Finset.univ.filter (fun t => P1 (rows t)))
        (Finset.univ.filter (fun t => P2 (rows t))) := by
      rw [Finset.disjoint_filter]
      intro t _ a1 a2
      exact hdis _ a1 a2
    have hu : Finset.univ.filter (fun t => P1 (rows t)) ∪ Finset.univ.filter (fun t => P2 (rows t)) ⊆
        Finset.univ.filter (fun t => ¬(i ∈ rows t ↔ j ∈ rows t)) := by
      intro t ht
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rcases ht with h | h
      · exact h1 _ h
      · exact h2 _ h
    have h5 := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hd] at h5
    omega
  rcases hdiam i j hij with hadj | ⟨v, hiv, hvj⟩
  · rcases hadj with h | h
    · refine two (fun y => i ∈ y ∧ j ∉ y) (fun y => i ∉ y ∧ j ∈ y) (fun y a1 a2 => a2.1 a1.1)
        (fun y a1 hh => a1.2 (hh.mp a1.1)) (fun y a1 hh => a1.1 (hh.mpr a1.2)) ?_ ?_
      · intro A hA
        obtain ⟨x, hx, h1, h2⟩ := hQ2 A hA (i, j) h true
        exact ⟨x, hx, by simpa using h1, by simpa using h2⟩
      · intro A hA
        obtain ⟨x, hx, h1, h2⟩ := hQ2 A hA (i, j) h false
        exact ⟨x, hx, by simpa using h1, by simpa using h2⟩
    · refine two (fun y => j ∈ y ∧ i ∉ y) (fun y => j ∉ y ∧ i ∈ y) (fun y a1 a2 => a2.1 a1.1)
        (fun y a1 hh => a1.2 (hh.mpr a1.1)) (fun y a1 hh => a1.1 (hh.mp a1.2)) ?_ ?_
      · intro A hA
        obtain ⟨x, hx, h1, h2⟩ := hQ2 A hA (j, i) h true
        exact ⟨x, hx, by simpa using h1, by simpa using h2⟩
      · intro A hA
        obtain ⟨x, hx, h1, h2⟩ := hQ2 A hA (j, i) h false
        exact ⟨x, hx, by simpa using h1, by simpa using h2⟩
  · have hjv : (j, v) ∈ E ∨ (v, j) ∈ E := hvj.symm
    refine two (fun y => v ∉ y ∧ ¬(i ∈ y ↔ j ∈ y)) (fun y => v ∈ y ∧ ¬(i ∈ y ↔ j ∈ y))
      (fun y a1 a2 => a1.1 a2.1) (fun y a1 => a1.2) (fun y a1 => a1.2) ?_ ?_
    · intro A hA
      obtain ⟨x, hx, h1, h2⟩ := hQ3 A hA i j v hij hiv hjv false
      exact ⟨x, hx, by simpa using h1, h2⟩
    · intro A hA
      obtain ⟨x, hx, h1, h2⟩ := hQ3 A hA i j v hij hiv hjv true
      exact ⟨x, hx, by simpa using h1, h2⟩
theorem sc_eq (y : Finset (Fin n)) :
    (Finset.univ.filter (fun p : Fin n × Fin n => ¬(p.1 ∈ y ↔ p.2 ∈ y))).card =
      2 * (y.card * (n - y.card)) := by
  have h : Finset.univ.filter (fun p : Fin n × Fin n => ¬(p.1 ∈ y ↔ p.2 ∈ y)) =
      (y ×ˢ (Finset.univ \ y)) ∪ ((Finset.univ \ y) ×ˢ y) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product,
      Finset.mem_sdiff]
    tauto
  have hd : Disjoint (y ×ˢ (Finset.univ \ y)) ((Finset.univ \ y) ×ˢ y) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at h1 h2
    exact h2.1 h1.1
  rw [h, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  ring
theorem mn_le (m : ℕ) (hm : m ≤ n) : m * (n - m) ≤ (n / 2) * (n - n / 2) := by
  have key : ∀ m', m' ≤ n / 2 → m' * (n - m') ≤ (n / 2) * (n - n / 2) := by
    intro m' hm'
    obtain ⟨d, hd⟩ : ∃ d, n / 2 = m' + d := ⟨n / 2 - m', by omega⟩
    have h2 : m' ≤ n - n / 2 := by omega
    have h1 : n - m' = (n - n / 2) + d := by omega
    rw [h1]
    generalize n - n / 2 = X at h2 ⊢
    rw [hd]
    nlinarith [Nat.mul_le_mul_left d h2]
  rcases Nat.lt_or_ge (n / 2) m with h | h
  · have h3 := key (n - m) (by omega)
    rwa [Nat.sub_sub_self hm, Nat.mul_comm (n - m) m] at h3
  · exact key m h
theorem dc {k : ℕ} [dW : DecidableEq (Finset (Fin n))] (rows : Fin k → Finset (Fin n)) (D : ℕ)
    (hs : ∀ i j : Fin n, i ≠ j → 2 * D ≤ (Finset.univ.filter (fun t => ¬(i ∈ rows t ↔ j ∈ rows t))).card) :
    2 * D * (n * n - n) ≤ (Finset.univ.filter (fun t => rows t ≠ ∅ ∧ rows t ≠ Finset.univ)).card *
      (2 * ((n / 2) * (n - n / 2))) := by
  have h1 : ∑ t, (Finset.univ.filter (fun p : Fin n × Fin n => ¬(p.1 ∈ rows t ↔ p.2 ∈ rows t))).card =
      ∑ p : Fin n × Fin n, (Finset.univ.filter (fun t => ¬(p.1 ∈ rows t ↔ p.2 ∈ rows t))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : 2 * D * (n * n - n) ≤
      ∑ p : Fin n × Fin n, (Finset.univ.filter (fun t => ¬(p.1 ∈ rows t ↔ p.2 ∈ rows t))).card := by
    have e : ∑ p : Fin n × Fin n, (if p.1 ≠ p.2 then 2 * D else 0) = 2 * D * (n * n - n) := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      have hc : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card = n * n - n := by
        have h3 : Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) =
            (Finset.univ : Finset (Fin n)).offDiag := by
          ext p
          simp [Finset.mem_offDiag]
        rw [h3, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      rw [hc, Nat.mul_comm]
    rw [← e]
    apply Finset.sum_le_sum
    intro p _
    split_ifs with h
    · exact hs p.1 p.2 h
    · exact Nat.zero_le _
  have h3 : ∀ t, (Finset.univ.filter (fun p : Fin n × Fin n => ¬(p.1 ∈ rows t ↔ p.2 ∈ rows t))).card ≤
      (if rows t ≠ ∅ ∧ rows t ≠ Finset.univ then 2 * ((n / 2) * (n - n / 2)) else 0) := by
    intro t
    rw [sc_eq]
    split_ifs with h
    · have h4 := mn_le (rows t).card (by simpa using Finset.card_le_univ (rows t))
      omega
    · rcases not_and_or.mp h with h' | h'
      · have h5 : rows t = ∅ := not_not.mp h'
        rw [h5]
        simp
      · have h5 : rows t = Finset.univ := not_not.mp h'
        rw [h5]
        simp
  have h4 : ∑ t, (if rows t ≠ ∅ ∧ rows t ≠ Finset.univ then 2 * ((n / 2) * (n - n / 2)) else 0) =
      (Finset.univ.filter (fun t => rows t ≠ ∅ ∧ rows t ≠ Finset.univ)).card *
        (2 * ((n / 2) * (n - n / 2))) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  calc 2 * D * (n * n - n) ≤ _ := h2
    _ = _ := h1.symm
    _ ≤ _ := Finset.sum_le_sum (fun t _ => h3 t)
    _ = _ := h4
theorem binid (hn : 2 ≤ n) :
    (n * n - n) * Nat.choose (n - 2) (n / 2 - 1) = (n / 2) * (n - n / 2) * Nat.choose n (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, (m + 2) / 2 = j + 1 := ⟨(m + 2) / 2 - 1, by omega⟩
  have hjm : j ≤ m := by omega
  rw [hj, show m + 2 - 2 = m by omega, show j + 1 - 1 = j by omega,
    show m + 2 - (j + 1) = m + 1 - j by omega]
  have e1 : (m + 2) * Nat.choose (m + 1) j = Nat.choose (m + 2) (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (m + 1) j
  have e2 : Nat.choose m j * (m + 1) = Nat.choose (m + 1) j * (m + 1 - j) := Nat.choose_mul_succ_eq m j
  have e3 : (m + 2) * (m + 2) - (m + 2) = (m + 2) * (m + 1) := by
    have h4 : (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) := by ring
    omega
  rw [e3]
  generalize m + 1 - j = q at e2 ⊢
  calc (m + 2) * (m + 1) * Nat.choose m j = (m + 2) * (Nat.choose m j * (m + 1)) := by ring
    _ = (m + 2) * (Nat.choose (m + 1) j * q) := by rw [e2]
    _ = ((m + 2) * Nat.choose (m + 1) j) * q := by ring
    _ = (Nat.choose (m + 2) (j + 1) * (j + 1)) * q := by rw [e1]
    _ = (j + 1) * q * Nat.choose (m + 2) (j + 1) := by ring
theorem lower {k : ℕ} {dk : DecidableEq (Fin k)} {dW : DecidableEq (Finset (Fin n))} (hn : 2 ≤ n)
    (E : Finset (Fin n × Fin n))
    (hdiam : ∀ i j : Fin n, i ≠ j → ((i, j) ∈ E ∨ (j, i) ∈ E) ∨
      ∃ v, ((i, v) ∈ E ∨ (v, i) ∈ E) ∧ ((v, j) ∈ E ∨ (j, v) ∈ E))
    (Q : Finset (Finset (Fin n)) → Prop)
    (hQ1 : ∀ A, Q A → ∅ ∈ A ∧ Finset.univ ∈ A)
    (hQ2 : ∀ A, Q A → ∀ e ∈ E, ∀ β : Bool, ∃ x ∈ A, (e.1 ∈ x ↔ β = true) ∧ (e.2 ∈ x ↔ β = false))
    (hQ3 : ∀ A, Q A → ∀ i j v : Fin n, i ≠ j → ((i, v) ∈ E ∨ (v, i) ∈ E) →
      ((j, v) ∈ E ∨ (v, j) ∈ E) → ∀ β : Bool, ∃ x ∈ A, (v ∈ x ↔ β = true) ∧ ¬(i ∈ x ↔ j ∈ x))
    (a : ℕ) (ha : 0 < a) (rows : Fin k → Finset (Fin n))
    (hrob : ∀ erased : Finset (Fin k), erased.card ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) - 1 →
      Q ((Finset.univ \ erased).image rows)) :
    2 * (2 * a * Nat.choose (n - 2) (n / 2 - 1)) + 2 * (a * Nat.choose n (n / 2)) ≤ k := by
  have hC : 0 < Nat.choose (n - 2) (n / 2 - 1) := Nat.choose_pos (by omega)
  have hD1 : 1 ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) ha) hC
  have hbin := binid hn
  generalize hDd : 2 * a * Nat.choose (n - 2) (n / 2 - 1) = D at hD1 hrob ⊢
  have hs : ∀ i j : Fin n, i ≠ j →
      2 * D ≤ (Finset.univ.filter (fun t => ¬(i ∈ rows t ↔ j ∈ rows t))).card :=
    fun i j hij => sep2 E hdiam Q hQ2 hQ3 D rows hrob hD1 i j hij
  have hdc := dc rows D hs
  have c0 : D - 1 < (Finset.univ.filter (fun t => rows t = ∅)).card :=
    cnt_rob rows (D - 1) Q hrob (fun y => y = ∅) (fun A hA => ⟨∅, (hQ1 A hA).1, rfl⟩)
  have c1 : D - 1 < (Finset.univ.filter (fun t => rows t = Finset.univ)).card :=
    cnt_rob rows (D - 1) Q hrob (fun y => y = Finset.univ) (fun A hA => ⟨Finset.univ, (hQ1 A hA).2, rfl⟩)
  have dAB : Disjoint (Finset.univ.filter (fun t => rows t = ∅))
      (Finset.univ.filter (fun t => rows t = Finset.univ)) := by
    rw [Finset.disjoint_filter]
    intro t _ h1 h2
    rw [h1] at h2
    have h3 := Finset.mem_univ (⟨0, by omega⟩ : Fin n)
    rw [← h2] at h3
    simp at h3
  have dABC : Disjoint (Finset.univ.filter (fun t => rows t = ∅) ∪
      Finset.univ.filter (fun t => rows t = Finset.univ))
      (Finset.univ.filter (fun t => rows t ≠ ∅ ∧ rows t ≠ Finset.univ)) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with h | h
    · exact h2.1 h
    · exact h2.2 h
  have h3 : (Finset.univ.filter (fun t => rows t = ∅)).card +
      (Finset.univ.filter (fun t => rows t = Finset.univ)).card +
      (Finset.univ.filter (fun t => rows t ≠ ∅ ∧ rows t ≠ Finset.univ)).card ≤ k := by
    rw [← Finset.card_union_of_disjoint dAB, ← Finset.card_union_of_disjoint dABC]
    exact (Finset.card_le_univ _).trans (by simp)
  have hX : 0 < (n / 2) * (n - n / 2) := Nat.mul_pos (by omega) (by omega)
  have e : 2 * D * (n * n - n) = (2 * (a * Nat.choose n (n / 2))) * (2 * ((n / 2) * (n - n / 2))) := by
    rw [← hDd]
    calc 2 * (2 * a * Nat.choose (n - 2) (n / 2 - 1)) * (n * n - n) =
        4 * a * ((n * n - n) * Nat.choose (n - 2) (n / 2 - 1)) := by ring
      _ = 4 * a * ((n / 2) * (n - n / 2) * Nat.choose n (n / 2)) := by rw [hbin]
      _ = (2 * (a * Nat.choose n (n / 2))) * (2 * ((n / 2) * (n - n / 2))) := by ring
  rw [e] at hdc
  have h4 := Nat.le_of_mul_le_mul_right hdc (by omega)
  omega
theorem main [DecidableEq (Finset (Fin n) → Bool)] {dW : DecidableEq (Finset (Fin n))}
    {dk : ∀ k, DecidableEq (Fin k)} (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hconn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ)
    (hdiam : ∀ i j : Fin n, i ≠ j → ((i, j) ∈ E ∨ (j, i) ∈ E) ∨
      ∃ v, ((i, v) ∈ E ∨ (v, i) ∈ E) ∧ ((v, j) ∈ E ∨ (j, v) ∈ E))
    (a b : ℕ) (ha : 0 < a) :
    (∃ k : ℕ, k ≤ b ∧ ∃ rows : Fin k → Finset (Fin n), ∀ erased : Finset (Fin k),
      erased.card ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) - 1 → KP E ((Finset.univ \ erased).image rows)) ↔
    2 * (2 * a * Nat.choose (n - 2) (n / 2 - 1)) + 2 * (a * Nat.choose n (n / 2)) ≤ b := by
  constructor
  · rintro ⟨k, hk, rows, hrob⟩
    have h1 := lower hn E hdiam (KP E) (fun A hA => nec_uni E hconn A hA)
      (fun A hA e he β => nec_edge E A hA e he β)
      (fun A hA i j v hij hiv hjv β => nec_path E hE A hA i j v hij hiv hjv β) a ha rows hrob
    omega
  · intro hb
    obtain ⟨k, hk, rows, hrows⟩ := upper hn E hE hconn a ha
    exact ⟨k, by omega, rows, hrows⟩
theorem mainA {dq : DecidableEq (Finset (Fin n) → Bool)} {dW : DecidableEq (Finset (Fin n))}
    {dk : ∀ k, DecidableEq (Fin k)} (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hconn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ)
    (bit neg : Fin n → Finset (Fin n) → Bool) (same : Fin n × Fin n → Finset (Fin n) → Bool)
    (hbit : ∀ i x, bit i x = true ↔ i ∈ x) (hneg : ∀ i x, neg i x = !(bit i x))
    (hsame : ∀ e x, same e x = (bit e.1 x == bit e.2 x))
    (raw need : Finset (Finset (Fin n) → Bool))
    (hraw : raw = {fun _ => false, fun _ => true} ∪ Finset.univ.image bit ∪ E.image same ∪
      E.image (fun e x => !(same e x)))
    (hneed : need = Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
      E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x))
    (hdiam : ∀ i j : Fin n, i ≠ j → ((i, j) ∈ E ∨ (j, i) ∈ E) ∨
      ∃ v, ((i, v) ∈ E ∨ (v, i) ∈ E) ∧ ((v, j) ∈ E ∨ (j, v) ∈ E))
    (a b : ℕ) (ha : 0 < a) :
    (∃ k : ℕ, k ≤ b ∧ ∃ rows : Fin k → Finset (Fin n), ∀ erased : Finset (Fin k),
      erased.card ≤ 2 * a * Nat.choose (n - 2) (n / 2 - 1) - 1 →
      ∀ (S : Finset (Fin n)) (p : ℕ),
        (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (raw ∪ S.image neg).toList.length C ∧
          C.output < (raw ∪ S.image neg).toList.length + C.size ∧ C.size ≤ p ∧
          ∀ f ∈ need, ∃ j < (raw ∪ S.image neg).toList.length + C.size,
            ∀ x ∈ (Finset.univ \ erased).image rows,
              (C.wires ((raw ∪ S.image neg).toList.map (fun g => g x))).getD j false = f x) ↔
        S.Nonempty ∧ n + 3 * E.card - S.card ≤ p) ↔
    2 * (2 * a * Nat.choose (n - 2) (n / 2 - 1)) + 2 * (a * Nat.choose n (n / 2)) ≤ b := by
  have hb : bit = bt := by
    funext i x
    exact Bool.eq_iff_iff.mpr (by rw [hbit]; simp [bt])
  subst hb
  have hn' : neg = ng := by
    funext i x
    rw [hneg]
    rfl
  subst hn'
  have hs : same = sm := by
    funext e x
    rw [hsame]
    rfl
  subst hs
  subst hraw
  subst hneed
  exact main hn E hE hconn hdiam a b ha
end Final
end PEqualNP.Outside.L_meta_53205
theorem PEqualNP.Outside.L_meta_53205 : ∀ (n : Nat) (E : Finset (Fin n × Fin n)), 2 ≤ n →
  (∀ e ∈ E, e.1 < e.2) →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    S.Nonempty ∧ n+3*E.card-S.card ≤ p
  let robust := fun (d b : Nat) => ∃ k : Nat, k ≤ b ∧ ∃ rows : Fin k → W,
    ∀ erased : Finset (Fin k), erased.card ≤ d → keeps ((Finset.univ \ erased).image rows)
  let adj := fun i j : Fin n => (i,j) ∈ E ∨ (j,i) ∈ E
  (∀ i j : Fin n, i ≠ j → adj i j ∨ ∃ v, adj i v ∧ adj v j) →
  ∀ (a b : Nat), 0 < a →
    let h := n/2
    let r := a * Nat.choose n h
    let D := 2*a*Nat.choose (n-2) (h-1)
    robust (D-1) b ↔ 2*D+2*r ≤ b := by
  intro n E hn hE hconn W bit neg same raw need keeps robust adj hdiam a b ha h r D
  exact PEqualNP.Outside.L_meta_53205.mainA hn E hE hconn bit neg same
    (fun i x => @decide_eq_true_iff _ (Classical.propDecidable _)) (fun _ _ => rfl)
    (fun e x => by simp [same, bit]) raw need rfl rfl hdiam a b ha
