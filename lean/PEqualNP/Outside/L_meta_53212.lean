import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53212

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (x : List Bool) (g : List Gate) (w : ℕ) : Bool :=
  ((⟨g, 0⟩ : Circuit).wires x).getD w false

def Ok (n : ℕ) (g : List Gate) : Prop :=
  (∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) ∧
  (∀ j (hj : j < g.length), ∀ i ∈ (g[j]).inputs, i < n + j)

def Ext (n : ℕ) (g g' : List Gate) : Prop :=
  Ok n g' ∧ g.length ≤ g'.length ∧ ∀ x : List Bool, x.length = n → ∀ w < n + g.length, val x g' w = val x g w

lemma wires_snoc (x : List Bool) (g : List Gate) (h : Gate) :
    (⟨g ++ [h], 0⟩ : Circuit).wires x =
      (⟨g, 0⟩ : Circuit).wires x ++ [h.op.eval (h.inputs.map fun i => val x g i)] := by
  simp [Circuit.wires, val, List.foldl_append]

lemma wires_length (x : List Bool) (g : List Gate) : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := by
  induction g using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton g h ih => rw [wires_snoc]; simp [ih]; omega

lemma Ext.refl {n g} (h : Ok n g) : Ext n g g := ⟨h, le_rfl, fun _ _ _ _ => rfl⟩

lemma Ext.trans {n g g' g''} (a : Ext n g g') (b : Ext n g' g'') : Ext n g g'' :=
  ⟨b.1, a.2.1.trans b.2.1, fun x hx w hw => by
    rw [b.2.2 x hx w (by have := a.2.1; omega), a.2.2 x hx w hw]⟩

lemma add_gate {n g} (hg : Ok n g) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (ha : a < n + g.length) (hb : b < n + g.length) :
    Ext n g (g ++ [⟨op, [a, b]⟩]) ∧ n + g.length < n + (g ++ [(⟨op, [a, b]⟩ : Gate)]).length ∧
      ∀ x : List Bool, x.length = n → val x (g ++ [⟨op, [a, b]⟩]) (n + g.length) = op.eval [val x g a, val x g b] := by
  refine ⟨⟨⟨?_, ?_⟩, by simp, ?_⟩, by simp, ?_⟩
  · intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hg.1 h hh
    · rw [List.mem_singleton.1 hh]; exact ⟨hop, by simp⟩
  · intro j hj i hi
    by_cases hlt : j < g.length
    · rw [List.getElem_append_left hlt] at hi
      exact hg.2 j hlt i hi
    · have : j = g.length := by simp at hj; omega
      subst this
      simp at hi
      rcases hi with rfl | rfl <;> assumption
  · intro x hx w hw
    unfold val
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length, hx]; exact hw)]
  · intro x hx
    have hl : ((⟨g, 0⟩ : Circuit).wires x).length = n + g.length := by rw [wires_length, hx]
    unfold val
    rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [hl])]
    simp [hl, val]

lemma chain_and {n g} (hg : Ok n g) (acc : ℕ) (l : List ℕ) (ha : acc < n + g.length) (hl : ∀ i ∈ l, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → val x g' w = (val x g acc && l.all (fun i => val x g i)) := by
  induction l generalizing g acc with
  | nil => exact ⟨g, acc, Ext.refl hg, ha, fun x _ => by simp⟩
  | cons i l ih =>
    have hi : i < n + g.length := by have := hl i (by simp); omega
    obtain ⟨e, hw, hv⟩ := add_gate hg GateOp.and (Or.inl rfl) acc i ha hi
    obtain ⟨g', w, e', hw', hv'⟩ := ih e.1 (n + g.length) hw (fun j hj => hl j (by simp [hj]))
    refine ⟨g', w, e.trans e', hw', fun x hx => ?_⟩
    rw [hv' x hx, hv x hx]
    have : l.all (fun j => val x (g ++ [⟨GateOp.and, [acc, i]⟩]) j) = l.all (fun j => val x g j) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H j hj
      · rw [← e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
      · rw [e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
    rw [this]
    simp [GateOp.eval, Bool.and_assoc]

def dnf (x : List Bool) (T : List (List ℕ)) : Bool := T.any (fun t => t.all (fun i => x.getD i false))

lemma val_input (x : List Bool) (g : List Gate) (i : ℕ) (hi : i < x.length) : val x g i = x.getD i false := by
  induction g using List.reverseRecOn with
  | nil => simp [val, Circuit.wires]
  | append_singleton g h ih =>
    unfold val at ih ⊢
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length]; omega)]
    exact ih

lemma build_dnf {n g} (hg : Ok n g) (f t : ℕ) (hf : f < n) (ht : t < n) (T : List (List ℕ))
    (hT : ∀ term ∈ T, ∀ i ∈ term, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → val x g' w = dnf x T := by
  induction T generalizing g with
  | nil =>
    refine ⟨g, f, Ext.refl hg, by omega, fun x hx h0 _ => ?_⟩
    rw [val_input x g f (by omega), h0]; simp [dnf]
  | cons term T ih =>
    obtain ⟨g1, r, e1, hr, hv1⟩ := ih hg (fun s hs => hT s (by simp [hs]))
    obtain ⟨g2, a, e2, ha, hv2⟩ := chain_and e1.1 t term (by omega) (hT term (by simp))
    have hr2 : r < n + g2.length := by have := e2.2.1; omega
    obtain ⟨e3, hw, hv3⟩ := add_gate e2.1 GateOp.or (Or.inr rfl) a r ha hr2
    refine ⟨_, _, (e1.trans e2).trans e3, hw, fun x hx h0 h1 => ?_⟩
    have hterm : term.all (fun i => val x g1 i) = term.all (fun i => x.getD i false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H i hi
      · rw [← val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
      · rw [val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
    rw [hv3 x hx, hv2 x hx, e2.2.2 x hx r hr, hv1 x hx h0 h1, hterm, val_input x g1 t (by omega), h1]
    simp [GateOp.eval, dnf]

lemma build_many {n} (f t : ℕ) (hf : f < n) (ht : t < n) : ∀ (k : ℕ) (T : Fin k → List (List ℕ)),
    (∀ j, ∀ term ∈ T j, ∀ i ∈ term, i < n) → ∀ g, Ok n g →
    ∃ g' : List Gate, ∃ o : Fin k → ℕ, Ext n g g' ∧ (∀ j, o j < n + g'.length) ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → ∀ j, val x g' (o j) = dnf x (T j) := by
  intro k
  induction k with
  | zero =>
    intro T _ g hg
    exact ⟨g, fun j => j.elim0, Ext.refl hg, fun j => j.elim0, fun _ _ _ _ j => j.elim0⟩
  | succ k ih =>
    intro T hT g hg
    obtain ⟨g1, w, e1, hw, hv1⟩ := build_dnf hg f t hf ht (T 0) (hT 0)
    obtain ⟨g2, o, e2, ho, hv2⟩ := ih (fun j => T j.succ) (fun j => hT j.succ) g1 e1.1
    refine ⟨g2, Fin.cases w o, e1.trans e2, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have := e2.2.1; simp; omega
      · simpa using ho j
    · intro x hx h0 h1 j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cases_zero]
        rw [e2.2.2 x hx w hw, hv1 x hx h0 h1]
      · simpa using hv2 x hx h0 h1 j

lemma circuit_mono (g : List Gate) (hg : ∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or))
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ w, x.getD w false = true → y.getD w false = true) :
    ∀ w, val x g w = true → val y g w = true := by
  induction g using List.reverseRecOn with
  | nil => simpa [val, Circuit.wires] using hxy
  | append_singleton g h ih =>
    have ih' := ih (fun k hk => hg k (by simp [hk]))
    intro w hw
    have lx : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := wires_length x g
    have ly : ((⟨g, 0⟩ : Circuit).wires y).length = x.length + g.length := by rw [wires_length, hl]
    unfold val at hw ⊢
    rw [wires_snoc] at hw ⊢
    by_cases hlt : w < x.length + g.length
    · rw [List.getD_append _ _ _ _ (by omega)] at hw ⊢
      exact ih' w hw
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hw ⊢
      rw [lx] at hw
      rw [ly]
      cases hk : w - (x.length + g.length) with
      | succ k => rw [hk] at hw; simp at hw
      | zero =>
        rw [hk] at hw
        simp only [List.getD_cons_zero] at hw ⊢
        rcases hg h (by simp) with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact ih' i (hw _ ⟨i, hi, rfl⟩)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hw ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, ih' i hb⟩

lemma reads_of_ok' {n : ℕ} {g : List Gate} (h : Ok n g) (o : ℕ) : ReadsBack n ⟨g, o⟩ := by
  intro j hj i hi
  have e : gateAt ⟨g, o⟩ j = g[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e] at hi
  exact h.2 j hj i hi

open Finset

lemma wire_of {α : Type} [DecidableEq (α → Bool)] (L : List (α → Bool)) (g : α → Bool) (hg : g ∈ L) (x : α) :
    L.idxOf g < L.length ∧ (L.map (fun h => h x)).getD (L.idxOf g) false = g x := by
  have lt := List.idxOf_lt_length_iff.2 hg
  refine ⟨lt, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem lt]
  simp

/-- El circuito de entradas L tiene un cable que calcula f en todas las asignaciones. -/
def Has {α : Type} (L : List (α → Bool)) (g : List Gate) (f : α → Bool) : Prop :=
  ∃ w, w < L.length + g.length ∧ ∀ x : α, val (L.map (fun h => h x)) g w = f x

lemma Has.mono {α : Type} {L : List (α → Bool)} {g g' : List Gate} {f : α → Bool}
    (e : Ext L.length g g') (h : Has L g f) : Has L g' f := by
  obtain ⟨w, hw, hv⟩ := h
  refine ⟨w, by have := e.2.1; omega, fun x => ?_⟩
  rw [e.2.2 _ (List.length_map _) w hw]
  exact hv x

lemma Has.input {α : Type} [DecidableEq (α → Bool)] {L : List (α → Bool)} (g : List Gate) {f : α → Bool}
    (h : f ∈ L) : Has L g f := by
  refine ⟨L.idxOf f, by have := List.idxOf_lt_length_iff.2 h; omega, fun x => ?_⟩
  have w := wire_of L f h x
  rw [val_input _ g _ (by rw [List.length_map]; exact w.1)]
  exact w.2

lemma Has.gate {α : Type} {L : List (α → Bool)} {g : List Gate} (ok : Ok L.length g) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) {a b f : α → Bool} (ha : Has L g a) (hb : Has L g b)
    (hf : ∀ x, op.eval [a x, b x] = f x) :
    ∃ g', Ext L.length g g' ∧ g'.length = g.length + 1 ∧ Has L g' f := by
  obtain ⟨i, hi, vi⟩ := ha
  obtain ⟨j, hj, vj⟩ := hb
  obtain ⟨e, hw, hv⟩ := add_gate ok op hop i j hi hj
  refine ⟨_, e, by simp, L.length + g.length, hw, fun x => ?_⟩
  rw [hv _ (List.length_map _), vi, vj]
  exact hf x

lemma sum_alpha (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (p : (¬a ∧ ¬b) ↔ (¬c ∧ ¬d)) (q : (¬¬a ∧ ¬¬b) ↔ (¬¬c ∧ ¬¬d)) :
    (if a then 1 else 0 : ℕ) + (if b then 1 else 0) = (if c then 1 else 0) + (if d then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;> simp [ha, hb, hc, hd] at p q ⊢

lemma sum_beta (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (p : (a ∧ ¬b) ↔ (c ∧ ¬d)) (q : (¬a ∧ ¬¬b) ↔ (¬c ∧ ¬¬d)) :
    (if a then 1 else 0 : ℕ) + (if d then 1 else 0) = (if c then 1 else 0) + (if b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;> simp [ha, hb, hc, hd] at p q ⊢

lemma neg_alpha (v a b : Prop) (p : ¬v ↔ (¬a ∧ ¬b)) (q : ¬¬v ↔ (¬¬a ∧ ¬¬b)) : a ↔ b := by
  by_cases hv : v <;> by_cases ha : a <;> by_cases hb : b <;> simp [hv, ha, hb] at p q ⊢

lemma card4 {α : Type} {inst : DecidableEq α} {A B C D : Finset α} {a b c d : ℕ}
    (h1 : A.card ≤ a) (h2 : B.card ≤ b) (h3 : C.card ≤ c) (h4 : D.card ≤ d) :
    (A ∪ B ∪ (C ∪ D)).card ≤ a + b + (c + d) :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2))
    ((Finset.card_union_le _ _).trans (Nat.add_le_add h3 h4)))

lemma memU {α : Type} {i : DecidableEq α} {A B : Finset α} {x : α} (h : x ∈ A ∨ x ∈ B) : x ∈ A ∪ B :=
  Finset.mem_union.2 h

lemma memI {α β : Type} {i : DecidableEq β} {s : Finset α} {f : α → β} {a : α} (h : a ∈ s) : f a ∈ s.image f :=
  Finset.mem_image_of_mem f h

lemma memSd {α : Type} {i : DecidableEq α} {s t : Finset α} {x : α} : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Finset.mem_sdiff

lemma memF {α : Type} {p : α → Prop} {i : DecidablePred p} {s : Finset α} {x : α} : x ∈ s.filter p ↔ x ∈ s ∧ p x :=
  Finset.mem_filter

/-- Compuertas AND que leen solo entradas. -/
lemma and_wires (x : List Bool) (ps : List (ℕ × ℕ)) (h : ∀ p ∈ ps, p.1 < x.length ∧ p.2 < x.length) :
    (⟨ps.map (fun p => ⟨GateOp.and, [p.1, p.2]⟩), 0⟩ : Circuit).wires x =
      x ++ ps.map (fun p => x.getD p.1 false && x.getD p.2 false) := by
  induction ps using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton ps p ih =>
    have ih' := ih (fun q hq => h q (by simp [hq]))
    obtain ⟨h1, h2⟩ := h p (by simp)
    rw [List.map_append, List.map_cons, List.map_nil, wires_snoc]
    unfold val
    rw [ih', List.map_append, ← List.append_assoc]
    congr 1
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]

lemma memI' {α β : Type} {i : DecidableEq β} {s : Finset α} {f : α → β} {b : β} (h : b ∈ s.image f) : ∃ a ∈ s, f a = b :=
  Finset.mem_image.1 h

lemma memI'' {α β : Type} {i : DecidableEq β} {s : Finset α} {f : α → β} {b : β} (h : b ∈ s.image f) : ∃ a ∈ s, f a = b :=
  Finset.mem_image.1 h

lemma memI'.symm' {α β : Type} {i : DecidableEq β} {s : Finset α} {f : α → β} {a : α} {b : β} (h : a ∈ s) (e : f a = b) :
    b ∈ s.image f :=
  Finset.mem_image.2 ⟨a, h, e⟩

lemma memIns {α : Type} {i : DecidableEq α} {s : Finset α} {a x : α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Finset.mem_insert

lemma memU' {α : Type} {i : DecidableEq α} {A B : Finset α} {x : α} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  Finset.mem_union

lemma cardU {α : Type} {i : DecidableEq α} {A B : Finset α} : (A ∪ B).card ≤ A.card + B.card :=
  Finset.card_union_le A B

end PEqualNP.Outside.L_meta_53212

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53212 : ∀ m : Nat, 0 < m →
  let n := m+m
  let E : Finset (Fin n × Fin n) := Finset.univ.image
    (fun i : Fin m => (Fin.castAdd m i, Fin.natAdd m i))
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
    (∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S) ∧ n+3*m-S.card ≤ p
  let K := Fin m → Fin 3
  let pat := fun (x : W) (i : Fin m) =>
    if bit (Fin.castAdd m i) x then
      (if bit (Fin.natAdd m i) x then 0 else 1 : Fin 3)
    else (if bit (Fin.natAdd m i) x then 2 else 0 : Fin 3)
  let admissible := fun P : Finset K =>
    let f := fun a : Fin m × Bool => P.filter (fun z => z a.1 = if a.2 then 2 else 1)
    Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
    (∀ i, ∃ z ∈ P, z i = 0) ∧
    ∀ a i, let u := f (i,false) ∪ f (i,true)
      f a ≠ u ∧ f a ≠ P \ u
  let flip := fun (i : Fin m) (x y : W) =>
    Fin.castAdd m i ∉ x ∧ Fin.natAdd m i ∉ x ∧
    y = insert (Fin.castAdd m i) (insert (Fin.natAdd m i) x)
  (∀ A : Finset W, keeps A ↔ admissible (A.image pat) ∧
      ∀ i, ∃ x ∈ A, ∃ y ∈ A, flip i x y) ∧
  ∀ (P : Finset K) (b : Nat),
    (∃ A : Finset W, A.image pat = P ∧ keeps A ∧ A.card ≤ b) ↔
      admissible P ∧ m+P.card ≤ b := by
  intro m hm n E W bit neg same raw need keeps K0 pat admissible flip
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
  letI dec2 : DecidableEq (Fin m → Fin 3) := fun a b => Classical.propDecidable (a = b)
  letI dec3 : DecidableEq K0 := dec2
  let c := m
  let color : Fin n → Fin c := Fin.addCases (fun i => i) (fun i => i)
  let U : Fin m → Fin n := fun i => Fin.castAdd m i
  let V : Fin m → Fin n := fun i => Fin.natAdd m i
  let ed : Fin m → Fin n × Fin n := fun i => (U i, V i)
  have colU : ∀ i, color (U i) = i := fun i => by simp only [color, U]; exact Fin.addCases_left i
  have colV : ∀ i, color (V i) = i := fun i => by simp only [color, V]; exact Fin.addCases_right i
  have cases_ : ∀ w : Fin n, w = U (color w) ∨ w = V (color w) := by
    intro w
    refine Fin.addCases (fun i => ?_) (fun i => ?_) w
    · exact Or.inl (by rw [show color (Fin.castAdd m i) = i from colU i])
    · exact Or.inr (by rw [show color (Fin.natAdd m i) = i from colV i])
  have UV : ∀ i, U i ≠ V i := by
    intro i h
    have := congrArg Fin.val h
    simp only [U, V, Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  have memE : ∀ i, ed i ∈ E := fun i =>
    PEqualNP.Outside.L_meta_53212.memI (Finset.mem_univ i)
  have ofE : ∀ e ∈ E, ∃ i, e = ed i := by
    intro e he
    obtain ⟨i, -, h⟩ := PEqualNP.Outside.L_meta_53212.memI' he
    exact ⟨i, h.symm⟩
  have edInj : Function.Injective ed := by
    intro i j h
    have := congrArg (fun e => color e.1) h
    simpa only [ed, colU] using this
  have cardE : E.card = m := by
    have e1 : E = Finset.univ.image ed := by
      ext e
      constructor
      · intro he
        obtain ⟨i, rfl⟩ := ofE e he
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · intro he
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
        exact memE i
    rw [e1, Finset.card_image_of_injective _ edInj, Finset.card_univ, Fintype.card_fin]
  have hsurj : Function.Surjective color := fun i => ⟨U i, colU i⟩
  have hcomp : ∀ (Z : Finset (Fin n)), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔ ∀ (i j : Fin n), color i = color j → (i ∈ Z ↔ j ∈ Z) := by
    intro Z
    constructor
    · intro h i j hc
      have toU : ∀ w, w ∈ Z ↔ U (color w) ∈ Z := by
        intro w
        rcases cases_ w with e | e
        · exact iff_of_eq (congrArg (· ∈ Z) e)
        · exact (iff_of_eq (congrArg (· ∈ Z) e)).trans (h _ (memE (color w))).symm
      rw [toU i, toU j, hc]
    · intro h e he
      obtain ⟨i, rfl⟩ := ofE e he
      exact h _ _ (by simp only [ed, colU, colV])
  have bitT : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have bitF : ∀ i x, bit i x = false ↔ i ∉ x := fun i x => by rw [← Bool.not_eq_true, bitT]
  have negT : ∀ i x, neg i x = true ↔ i ∉ x := fun i x => by simp [neg, bitF]
  have negF : ∀ i x, neg i x = false ↔ i ∈ x := fun i x => by simp [neg, bitT]
  have sameT : ∀ e x, same e x = true ↔ (e.1 ∈ x ↔ e.2 ∈ x) := by
    intro e x
    simp only [same, beq_iff_eq]
    rw [Bool.eq_iff_iff, bitT, bitT]
  have edgeColor : ∀ e ∈ E, color e.1 = color e.2 := by
    intro e he
    have := (hcomp (Finset.univ.filter (fun i => color i = color e.1))).2 (fun i j h => by simp [h]) e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, true_iff] at this
    exact this.symm
  have rawF : (fun _ => false : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_insert_self _ _))))))
  have rawT : (fun _ => true : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))))
  have rawB : ∀ i, bit i ∈ raw := fun i =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
  have rawS : ∀ e ∈ E, same e ∈ raw := fun e he =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
  have rawD : ∀ e ∈ E, (fun x => !(same e x)) ∈ raw := fun e he =>
    Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
  -- atomos
  let atom : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q =>
    ![fun x => neg q.1.1 x && neg q.1.2 x, fun x => bit q.1.1 x && neg q.1.2 x, fun x => neg q.1.1 x && bit q.1.2 x] q.2
  have a0 : ∀ e x, atom (e, 0) x = true ↔ e.1 ∉ x ∧ e.2 ∉ x := fun e x => by
    show (neg e.1 x && neg e.2 x) = true ↔ _
    rw [Bool.and_eq_true, negT, negT]
  have a1 : ∀ e x, atom (e, 1) x = true ↔ e.1 ∈ x ∧ e.2 ∉ x := fun e x => by
    show (bit e.1 x && neg e.2 x) = true ↔ _
    rw [Bool.and_eq_true, bitT, negT]
  have a2 : ∀ e x, atom (e, 2) x = true ↔ e.1 ∉ x ∧ e.2 ∈ x := fun e x => by
    show (neg e.1 x && bit e.2 x) = true ↔ _
    rw [Bool.and_eq_true, negT, bitT]
  let Kc : Fin m → Finset (Fin n) := fun j => Finset.univ.filter (fun i => color i = j)
  have mK : ∀ j w, w ∈ Kc j ↔ color w = j := fun j w =>
    ⟨fun h => (PEqualNP.Outside.L_meta_53212.memF.1 h).2,
      fun h => PEqualNP.Outside.L_meta_53212.memF.2 ⟨Finset.mem_univ _, h⟩⟩
  have patG : ∀ (x : W) i (s t : Bool), bit (U i) x = s → bit (V i) x = t →
      pat x i = if s then (if t then 0 else 1) else (if t then 2 else 0) := by
    intro x i s t h1 h2
    have h1' : bit (Fin.castAdd m i) x = s := h1
    have h2' : bit (Fin.natAdd m i) x = t := h2
    simp only [pat, h1', h2']
  have pat1 : ∀ (x : W) i, pat x i = 1 ↔ U i ∈ (x : Finset (Fin n)) ∧ V i ∉ (x : Finset (Fin n)) := by
    intro x i
    have p : bit (U i) x = true ↔ U i ∈ (x : Finset (Fin n)) := bitT _ _
    have q : bit (V i) x = true ↔ V i ∈ (x : Finset (Fin n)) := bitT _ _
    rw [← p, ← q]
    cases hs : bit (U i) x <;> cases ht : bit (V i) x <;> rw [patG x i _ _ hs ht] <;> simp
  have pat2 : ∀ (x : W) i, pat x i = 2 ↔ U i ∉ (x : Finset (Fin n)) ∧ V i ∈ (x : Finset (Fin n)) := by
    intro x i
    have p : bit (U i) x = true ↔ U i ∈ (x : Finset (Fin n)) := bitT _ _
    have q : bit (V i) x = true ↔ V i ∈ (x : Finset (Fin n)) := bitT _ _
    rw [← p, ← q]
    cases hs : bit (U i) x <;> cases ht : bit (V i) x <;> rw [patG x i _ _ hs ht] <;> simp
  have pat0 : ∀ (x : W) i, pat x i = 0 ↔ (U i ∈ (x : Finset (Fin n)) ↔ V i ∈ (x : Finset (Fin n))) := by
    intro x i
    have p : bit (U i) x = true ↔ U i ∈ (x : Finset (Fin n)) := bitT _ _
    have q : bit (V i) x = true ↔ V i ∈ (x : Finset (Fin n)) := bitT _ _
    rw [← p, ← q]
    cases hs : bit (U i) x <;> cases ht : bit (V i) x <;> rw [patG x i _ _ hs ht] <;> simp
  let kv : Bool → Fin 3 := fun s => if s then 2 else 1
  have kvF : kv false = 1 := rfl
  have kvT : kv true = 2 := rfl
  have kv0 : ∀ s, kv s ≠ 0 := fun s => by
    cases s
    · rw [kvF]; decide
    · rw [kvT]; decide
  let G : Finset K0 → Fin m × Bool → Finset K0 := fun P a =>
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    P.filter (fun z => z a.1 = if a.2 then 2 else 1)
  have mG : ∀ (P : Finset K0) (a : Fin m × Bool) (z : K0), z ∈ G P a ↔ z ∈ P ∧ z a.1 = kv a.2 := by
    intro P a z
    refine PEqualNP.Outside.L_meta_53212.memF.trans (and_congr_right' ?_)
    obtain ⟨j, s⟩ := a
    cases s <;> simp [kvF, kvT]
  have atomPat : ∀ i s (x : W), atom (ed i, kv s) x = true ↔ pat x i = kv s := by
    intro i s x
    cases s
    · rw [kvF, a1, pat1]
    · rw [kvT, a2, pat2]
  have kOf : ∀ k : Fin 3, k ≠ 0 → ∃ s, k = kv s := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact ⟨false, kvF.symm⟩
    · exact ⟨true, kvT.symm⟩
  have kvInj : ∀ s t, kv s = kv t → s = t := by
    intro s t h
    cases s <;> cases t
    · rfl
    · rw [kvF, kvT] at h; exact absurd h (by decide)
    · rw [kvT, kvF] at h; exact absurd h (by decide)
    · rfl
  have cond : ∀ (S : Finset (Fin n)) (p : ℕ),
      ((∀ i : Fin m, U i ∈ S ∨ V i ∈ S) ∧ n+3*m-S.card ≤ p) ↔
      ((∀ j : Fin c, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p) := by
    intro S p
    rw [cardE]
    refine and_congr_left' ⟨fun h j => ?_, fun h j => ?_⟩
    · rcases h j with h | h
      · exact ⟨_, h, colU j⟩
      · exact ⟨_, h, colV j⟩
    · obtain ⟨w, hw, hc⟩ := h j
      rcases cases_ w with e | e
      · rw [hc] at e; exact Or.inl (e ▸ hw)
      · rw [hc] at e; exact Or.inr (e ▸ hw)
  have build : ∀ (B : Finset W) (S : Finset (Fin n)) (p : ℕ),
      ((∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (raw ∪ S.image neg).toList.length C ∧
        C.output < (raw ∪ S.image neg).toList.length+C.size ∧ C.size ≤ p ∧
        ∀ f ∈ need, ∃ j < (raw ∪ S.image neg).toList.length+C.size,
          ∀ x ∈ B, (C.wires ((raw ∪ S.image neg).toList.map (fun g => g x))).getD j false = f x := by
    intro B S p
    let L := (raw ∪ S.image neg).toList
    have inL : ∀ g, g ∈ raw ∨ g ∈ S.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
    rintro ⟨meets, budget⟩
    have inRaw : ∀ g ∈ raw, g ∈ L := fun g h => inL g (Or.inl h)
    have ok0 : PEqualNP.Outside.L_meta_53212.Ok L.length [] := ⟨by simp, by simp⟩
    let Has := fun (g : List PEqualNP.CircuitLowerBounds.Gate) (f : W → Bool) => PEqualNP.Outside.L_meta_53212.Has L g f
    -- tres atomos de una arista con cuatro entradas disponibles
    have three : ∀ g, PEqualNP.Outside.L_meta_53212.Ok L.length g → ∀ e : Fin n × Fin n, ∀ a b c' d e' f' : W → Bool,
        Has g a → Has g b → Has g c' → Has g d → Has g e' → Has g f' →
        (∀ x, (a x && b x) = atom (e, 0) x) → (∀ x, (c' x && d x) = atom (e, 1) x) → (∀ x, (e' x && f' x) = atom (e, 2) x) →
        ∃ g', PEqualNP.Outside.L_meta_53212.Ext L.length g g' ∧ g'.length = g.length + 3 ∧ ∀ k, Has g' (atom (e, k)) := by
      intro g ok e a b c' d e' f' ha hb hc hd he hf q0 q1 q2
      obtain ⟨g1, x1, l1, h1⟩ := PEqualNP.Outside.L_meta_53212.Has.gate ok PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) ha hb
        (f := atom (e, 0)) (fun x => by rw [← q0]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g2, x2, l2, h2⟩ := PEqualNP.Outside.L_meta_53212.Has.gate x1.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
        (hc.mono x1) (hd.mono x1) (f := atom (e, 1)) (fun x => by rw [← q1]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g3, x3, l3, h3⟩ := PEqualNP.Outside.L_meta_53212.Has.gate x2.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
        (he.mono (x1.trans x2)) (hf.mono (x1.trans x2)) (f := atom (e, 2)) (fun x => by rw [← q2]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      refine ⟨g3, (x1.trans x2).trans x3, by omega, fun k => ?_⟩
      fin_cases k
      · exact h1.mono (x2.trans x3)
      · exact h2.mono x3
      · exact h3
    have val3 : ∀ (e : Fin n × Fin n) (x : W), atom (e, 0) x = (!(bit e.1 x) && !(bit e.2 x)) ∧
        atom (e, 1) x = (bit e.1 x && !(bit e.2 x)) ∧ atom (e, 2) x = (!(bit e.1 x) && bit e.2 x) :=
      fun e x => ⟨rfl, rfl, rfl⟩
    have sameBit : ∀ (e : Fin n × Fin n) (x : W), same e x = (bit e.1 x == bit e.2 x) := by
      intro e x
      rw [Bool.eq_iff_iff, sameT, beq_iff_eq, Bool.eq_iff_iff, bitT, bitT]
    have grow : ∀ m, ∀ (T : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (g : List PEqualNP.CircuitLowerBounds.Gate),
        (Tᶜ).card = m → S ⊆ T → F ⊆ E → (∀ e ∈ F, e.1 ∈ T ∧ e.2 ∈ T) → PEqualNP.Outside.L_meta_53212.Ok L.length g →
        (∀ v ∈ T, Has g (neg v)) → (∀ e ∈ F, ∀ k, Has g (atom (e, k))) → g.length + S.card = 3 * F.card + T.card →
        ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
          PEqualNP.Outside.L_meta_53212.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
          g'.length + S.card = 3 * F'.card + n := by
      intro m
      induction m with
      | zero =>
        intro T F g hm _ hF _ ok hn ha len
        have full : T = Finset.univ := by
          rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at hm
          · exact hm
        refine ⟨F, g, hF, ok, fun v => hn v (full ▸ Finset.mem_univ v), ha, ?_⟩
        rw [full, Finset.card_univ, Fintype.card_fin] at len
        exact len
      | succ m ih =>
        intro T F g hm hS hF hFT ok hn ha len
        have cross : ∃ e ∈ E, ¬ (e.1 ∈ T ↔ e.2 ∈ T) := by
          by_contra hno
          have closed : ∀ e ∈ E, e.1 ∈ T ↔ e.2 ∈ T := fun e he => by
            by_contra h
            exact hno ⟨e, he, h⟩
          have inv := (hcomp T).1 closed
          have : T = Finset.univ := by
            refine Finset.eq_univ_of_forall (fun v => ?_)
            obtain ⟨s, hs, cs⟩ := meets (color v)
            exact (inv s v cs).1 (hS hs)
          rw [this, Finset.compl_univ, Finset.card_empty] at hm
          omega
        obtain ⟨e, he, hx⟩ := cross
        have eF : e ∉ F := fun h => hx (iff_of_true (hFT e h).1 (hFT e h).2)
        have bitHas : ∀ i, Has g (bit i) := fun i => PEqualNP.Outside.L_meta_53212.Has.input g (inRaw _ (rawB i))
        have sHas : Has g (same e) := PEqualNP.Outside.L_meta_53212.Has.input g (inRaw _ (rawS e he))
        have dHas : Has g (fun x => !(same e x)) := PEqualNP.Outside.L_meta_53212.Has.input g (inRaw _ (rawD e he))
        have step : ∀ v, v ∉ T → (v = e.1 ∨ v = e.2) → (∀ w, (w = e.1 ∨ w = e.2) → w ≠ v → w ∈ T) →
            ∀ g3 : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.Outside.L_meta_53212.Ext L.length g g3 → g3.length = g.length + 3 →
            (∀ k, Has g3 (atom (e, k))) → ∀ i j : Fin 3, (∀ x, (atom (e, i) x || atom (e, j) x) = neg v x) →
            ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
              PEqualNP.Outside.L_meta_53212.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
              g'.length + S.card = 3 * F'.card + n := by
          intro v vT vend other g3 x3 l3 h3 i j hor
          obtain ⟨g4, x4, l4, h4⟩ := PEqualNP.Outside.L_meta_53212.Has.gate x3.1 PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl)
            (h3 i) (h3 j) (f := neg v) (fun x => by rw [← hor]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
          have inT : ∀ w, (w = e.1 ∨ w = e.2) → w ∈ insert v T := by
            intro w hw
            by_cases h : w = v
            · rw [h]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (other w hw h)
          have cm : ((insert v T)ᶜ).card = m := by
            rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.2 vT), hm]
            rfl
          refine ih (insert v T) (insert e F) g4 cm (hS.trans (Finset.subset_insert _ _)) (Finset.insert_subset he hF) ?_ x4.1 ?_ ?_ ?_
          · intro f hf
            rcases Finset.mem_insert.1 hf with rfl | hf
            · exact ⟨inT _ (Or.inl rfl), inT _ (Or.inr rfl)⟩
            · exact ⟨Finset.mem_insert_of_mem (hFT f hf).1, Finset.mem_insert_of_mem (hFT f hf).2⟩
          · intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact h4
            · exact (hn w hw).mono (x3.trans x4)
          · intro f hf k
            rcases Finset.mem_insert.1 hf with rfl | hf
            · exact (h3 k).mono x4
            · exact (ha f hf k).mono (x3.trans x4)
          · rw [Finset.card_insert_of_notMem eF, Finset.card_insert_of_notMem vT, l4, l3]
            omega
        by_cases h1 : e.1 ∈ T
        · have h2 : e.2 ∉ T := fun h => hx (iff_of_true h1 h)
          have nu := hn _ h1
          obtain ⟨g3, x3, l3, h3⟩ := three g ok e (same e) (neg e.1) (fun x => !(same e x)) (bit e.1) (fun x => !(same e x)) (neg e.1)
            sHas nu dHas (bitHas _) dHas nu
            (fun x => by
              rw [(val3 e x).1, sameBit]; show ((bit e.1 x == bit e.2 x) && !(bit e.1 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.1, sameBit]
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.2, sameBit]; show ((!(bit e.1 x == bit e.2 x)) && !(bit e.1 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
          refine step e.2 h2 (Or.inr rfl) (fun w hw hne => ?_) g3 x3 l3 h3 0 1 (fun x => ?_)
          · rcases hw with rfl | rfl
            · exact h1
            · exact absurd rfl hne
          · rw [(val3 e x).1, (val3 e x).2.1]
            show _ = !(bit e.2 x)
            cases bit e.1 x <;> cases bit e.2 x <;> rfl
        · have h2 : e.2 ∈ T := by
            by_contra h
            exact hx (iff_of_false h1 h)
          have nv := hn _ h2
          obtain ⟨g3, x3, l3, h3⟩ := three g ok e (same e) (neg e.2) (fun x => !(same e x)) (neg e.2) (fun x => !(same e x)) (bit e.2)
            sHas nv dHas nv dHas (bitHas _)
            (fun x => by
              rw [(val3 e x).1, sameBit]; show ((bit e.1 x == bit e.2 x) && !(bit e.2 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.1, sameBit]; show ((!(bit e.1 x == bit e.2 x)) && !(bit e.2 x)) = _
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
            (fun x => by
              rw [(val3 e x).2.2, sameBit]
              cases bit e.1 x <;> cases bit e.2 x <;> rfl)
          refine step e.1 h1 (Or.inl rfl) (fun w hw hne => ?_) g3 x3 l3 h3 0 2 (fun x => ?_)
          · rcases hw with rfl | rfl
            · exact absurd rfl hne
            · exact h2
          · rw [(val3 e x).1, (val3 e x).2.2]
            show _ = !(bit e.1 x)
            cases bit e.1 x <;> cases bit e.2 x <;> rfl
    obtain ⟨F, g, hF, ok, hn, ha, len⟩ := grow _ S ∅ [] rfl (Finset.Subset.refl _) (Finset.empty_subset _) (by simp) ok0
      (fun v hv => PEqualNP.Outside.L_meta_53212.Has.input [] (inL _ (Or.inr (Finset.mem_image_of_mem _ hv))))
      (by simp) (by simp)
    have rest : ∀ R : Finset (Fin n × Fin n), R ⊆ E → Disjoint F R →
        ∃ g', PEqualNP.Outside.L_meta_53212.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F ∪ R, ∀ k, Has g' (atom (e, k))) ∧
          g'.length + S.card = 3 * (F ∪ R).card + n := by
      intro R
      induction R using Finset.induction with
      | empty =>
        intro _ _
        exact ⟨g, ok, hn, by simpa using ha, by simpa using len⟩
      | insert e R heR ih =>
        intro hsub hdis
        obtain ⟨g1, ok1, n1, at1, l1⟩ := ih ((Finset.subset_insert _ _).trans hsub)
          (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdis)
        have he : e ∈ E := hsub (Finset.mem_insert_self _ _)
        have eF : e ∉ F := fun h => Finset.disjoint_left.1 hdis h (Finset.mem_insert_self _ _)
        have bitHas : ∀ i, Has g1 (bit i) := fun i => PEqualNP.Outside.L_meta_53212.Has.input g1 (inRaw _ (rawB i))
        obtain ⟨g3, x3, l3, h3⟩ := three g1 ok1 e (neg e.1) (neg e.2) (bit e.1) (neg e.2) (neg e.1) (bit e.2)
          (n1 _) (n1 _) (bitHas _) (n1 _) (n1 _) (bitHas _) (fun x => rfl) (fun x => rfl) (fun x => rfl)
        refine ⟨g3, x3.1, fun v => (n1 v).mono x3, ?_, ?_⟩
        · intro f hf k
          rcases Finset.mem_union.1 hf with hf | hf
          · exact (at1 f (Finset.mem_union_left _ hf) k).mono x3
          rcases Finset.mem_insert.1 hf with rfl | hf
          · exact h3 k
          · exact (at1 f (Finset.mem_union_right _ hf) k).mono x3
        · have ne : e ∉ F ∪ R := fun h => (Finset.mem_union.1 h).elim eF heR
          rw [Finset.union_insert, Finset.card_insert_of_notMem ne, l3]
          omega
    obtain ⟨g', ok', hn', ha', len'⟩ := rest (E \ F) Finset.sdiff_subset Finset.disjoint_sdiff
    have all : F ∪ (E \ F) = E := Finset.union_sdiff_of_subset hF
    rw [all] at ha' len'
    have Lpos : 0 < L.length := lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.2 (inRaw _ rawF))
    have Sn : S.card ≤ n := by simpa using Finset.card_le_univ S
    refine ⟨⟨g', 0⟩, ?_, PEqualNP.Outside.L_meta_53212.reads_of_ok' ok' 0, ?_, ?_, ?_⟩
    · intro x hx
      have := ok'.1 x hx
      exact ⟨by simpa using this.1, this.2⟩
    · show 0 < L.length + g'.length
      omega
    · show g'.length ≤ p
      omega
    · intro f hf
      have out : Has g' f := by
        rcases Finset.mem_union.1 hf with hf | hf
        · rcases Finset.mem_union.1 hf with hf | hf
          · rcases Finset.mem_union.1 hf with hf | hf
            · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hf
              exact hn' v
            · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
              exact ha' e he 0
          · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
            exact ha' e he 1
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
          exact ha' e he 2
      obtain ⟨w, hw, hv⟩ := out
      exact ⟨w, hw, fun x _ => hv x⟩
  have equiv : ∀ A : Finset W, keeps A ↔ admissible (A.image pat) ∧ ∀ i, ∃ x ∈ A, ∃ y ∈ A, flip i x y := by
    intro A
    have flipEq : ∀ i (x y : W), flip i x y → Disjoint (x : Finset (Fin n)) (Kc i) ∧ (y : Finset (Fin n)) = (x : Finset (Fin n)) ∪ Kc i := by
      intro i x y h
      obtain ⟨h1, h2, h3⟩ := h
      constructor
      · rw [Finset.disjoint_right]
        intro w hw
        have cw := (mK i w).1 hw
        rcases cases_ w with e | e
        · rw [cw] at e; rw [e]; exact h1
        · rw [cw] at e; rw [e]; exact h2
      · ext w
        have : (y : Finset (Fin n)) = insert (U i) (insert (V i) (x : Finset (Fin n))) := by
          rw [h3]; ext v; exact (PEqualNP.Outside.L_meta_53212.memIns.trans (or_congr_right PEqualNP.Outside.L_meta_53212.memIns)).trans (PEqualNP.Outside.L_meta_53212.memIns.trans (or_congr_right PEqualNP.Outside.L_meta_53212.memIns)).symm
        rw [this]
        constructor
        · intro hw
          refine Finset.mem_union.2 ?_
          by_cases a : w = U i
          · exact Or.inr ((mK i w).2 (by rw [a, colU]))
          by_cases b : w = V i
          · exact Or.inr ((mK i w).2 (by rw [b, colV]))
          refine Or.inl ?_
          rcases PEqualNP.Outside.L_meta_53212.memIns.1 hw with h | h
          · exact absurd h a
          rcases PEqualNP.Outside.L_meta_53212.memIns.1 h with h | h
          · exact absurd h b
          exact h
        · intro hw
          rcases Finset.mem_union.1 hw with h | h
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
          · have cw := (mK i w).1 h
            rcases cases_ w with e | e
            · rw [cw] at e; rw [e]; exact Finset.mem_insert_self _ _
            · rw [cw] at e; rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have toFlip : ∀ i (x y : W), Disjoint (x : Finset (Fin n)) (Kc i) → (y : Finset (Fin n)) = (x : Finset (Fin n)) ∪ Kc i → flip i x y := by
      intro i x y h1 h2
      have u : U i ∈ Kc i := (mK _ _).2 (colU i)
      have v : V i ∈ Kc i := (mK _ _).2 (colV i)
      refine ⟨fun h => Finset.disjoint_left.1 h1 h u, fun h => Finset.disjoint_left.1 h1 h v, ?_⟩
      show (y : Finset (Fin n)) = _
      rw [h2]
      ext w
      constructor
      · intro hw
        rcases Finset.mem_union.1 hw with h | h
        · exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr (PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr h)))
        · have cw := (mK i w).1 h
          rcases cases_ w with e | e
          · rw [cw] at e; exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inl e)
          · rw [cw] at e
            exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr (PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inl e)))
      · intro hw
        refine Finset.mem_union.2 ?_
        rcases PEqualNP.Outside.L_meta_53212.memIns.1 hw with h | h
        · exact Or.inr (h ▸ u)
        rcases PEqualNP.Outside.L_meta_53212.memIns.1 h with h | h
        · exact Or.inr (h ▸ v)
        · exact Or.inl h
    have fP : ∀ (a : Fin m × Bool) (x : W), x ∈ A →
        (pat x ∈ G (A.image pat) a ↔ atom (ed a.1, kv a.2) x = true) := by
      intro a x hx
      rw [mG, atomPat]
      exact and_iff_right (PEqualNP.Outside.L_meta_53212.memI hx)
    constructor
    · intro hk0
      have hk : ∀ (S : Finset (Fin n)) (p : ℕ),
          (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (raw ∪ S.image neg).toList.length C ∧
            C.output < (raw ∪ S.image neg).toList.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < (raw ∪ S.image neg).toList.length+C.size,
              ∀ x ∈ A, (C.wires ((raw ∪ S.image neg).toList.map (fun g => g x))).getD j false = f x) ↔
          ((∀ j : Fin c, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p) :=
        fun S p => (hk0 S p).trans (cond S p)
      have hne : E.Nonempty := ⟨_, memE ⟨0, hm⟩⟩
      have universal : ∀ L : List (W → Bool), (fun _ => false) ∈ L → (fun _ => true) ∈ L →
          (∀ f ∈ need, ∀ x ∈ A, ∀ y ∈ A, (∀ g ∈ L, g x = true → g y = true) → f x = true → f y = true) →
          ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
            C.output < L.length+C.size ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
              ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
        intro L hf ht mono
        have f0 := List.idxOf_lt_length_iff.2 hf
        have t0 := List.idxOf_lt_length_iff.2 ht
        let ord := need.equivFin
        let T : Fin need.card → List (List ℕ) := fun k =>
          (A.toList.filter (fun x => decide ((ord.symm k).1 x = true))).map
            (fun x => (List.range L.length).filter (fun i => (L.map (fun g => g x)).getD i false))
        have bnd : ∀ k, ∀ term ∈ T k, ∀ i ∈ term, i < L.length := by
          intro k term hterm i hi
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hterm
          exact List.mem_range.1 (List.mem_filter.1 hi).1
        have ok0 : PEqualNP.Outside.L_meta_53212.Ok L.length [] := ⟨by simp, by simp⟩
        obtain ⟨g, o, ext, ho, hv⟩ := PEqualNP.Outside.L_meta_53212.build_many (n := L.length) _ _ f0 t0 need.card T bnd [] ok0
        have f1 := List.idxOf_lt_length_iff.2 hf
        refine ⟨⟨g, L.idxOf (fun _ => false)⟩, ?_, PEqualNP.Outside.L_meta_53212.reads_of_ok' ext.1 _, ?_, ?_⟩
        · intro h hh
          have := ext.1.1 h hh
          exact ⟨by simpa using this.1, this.2⟩
        · show L.idxOf (fun _ => false) < L.length + g.length
          omega
        · intro f hfn
          refine ⟨o (ord ⟨f, hfn⟩), ho _, fun y hy => ?_⟩
          have len : (L.map (fun g => g y)).length = L.length := List.length_map _
          have e0 := (PEqualNP.Outside.L_meta_53212.wire_of L _ hf y).2
          have e1 := (PEqualNP.Outside.L_meta_53212.wire_of L _ ht y).2
          have key := hv _ len e0 e1 (ord ⟨f, hfn⟩)
          change PEqualNP.Outside.L_meta_53212.val (L.map (fun g => g y)) g (o (ord ⟨f, hfn⟩)) = f y
          rw [key, Bool.eq_iff_iff]
          unfold PEqualNP.Outside.L_meta_53212.dnf
          rw [List.any_eq_true]
          simp only [T, Equiv.symm_apply_apply]
          constructor
          · rintro ⟨term, hterm, hall⟩
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hterm
            obtain ⟨hxA, hfx⟩ := List.mem_filter.1 hx
            refine mono f hfn x (Finset.mem_toList.1 hxA) y hy (fun h hh hx1 => ?_) (of_decide_eq_true hfx)
            have wx := PEqualNP.Outside.L_meta_53212.wire_of L h hh x
            have wy := PEqualNP.Outside.L_meta_53212.wire_of L h hh y
            have := List.all_eq_true.1 hall (L.idxOf h) (List.mem_filter.2 ⟨List.mem_range.2 wx.1, by rw [wx.2]; exact hx1⟩)
            rw [wy.2] at this
            exact this
          · intro hfy
            refine ⟨_, List.mem_map.2 ⟨y, List.mem_filter.2 ⟨Finset.mem_toList.2 hy, decide_eq_true hfy⟩, rfl⟩, ?_⟩
            exact List.all_eq_true.2 (fun i hi => (List.mem_filter.1 hi).2)
      -- (1) cada componente se voltea entre dos asignaciones de la muestra
      have flips : ∀ j : Fin c, ∃ x ∈ A, Disjoint x (Finset.univ.filter (fun i => color i = j)) ∧
          x ∪ Finset.univ.filter (fun i => color i = j) ∈ A := by
        intro j
        by_contra hno
        set K := Finset.univ.filter (fun i => color i = j) with hK
        set S : Finset (Fin n) := Finset.univ.filter (fun i => color i ≠ j) with hS
        let L := (raw ∪ S.image neg).toList
        have mem : ∀ g, g ∈ raw ∨ g ∈ S.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
        have hf : (fun _ => false : W → Bool) ∈ raw := rawF
        have ht : (fun _ => true : W → Bool) ∈ raw := rawT
        obtain ⟨C, c1, c2, c3, c4⟩ := universal L (mem _ (Or.inl hf)) (mem _ (Or.inl ht)) (by
          intro f hfn x hx y hy hle hfx
          have hbit : ∀ i, i ∈ x → i ∈ y := by
            intro i hi
            have m : bit i ∈ raw := rawB i
            exact (bitT i y).1 (hle _ (mem _ (Or.inl m)) ((bitT i x).2 hi))
          have hsame : ∀ e ∈ E, same e x = same e y := by
            intro e he
            have m1 : same e ∈ raw :=
              Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
            have m2 : (fun x => !(same e x)) ∈ raw :=
              Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
            have a := hle _ (mem _ (Or.inl m1))
            have b := hle _ (mem _ (Or.inl m2))
            cases h1 : same e x
            · rw [h1] at b
              simp only [Bool.not_false, true_implies, Bool.not_eq_true'] at b
              exact b.symm
            · exact (a h1).symm
          have hS' : ∀ i, color i ≠ j → i ∈ y → i ∈ x := by
            intro i hi hy'
            by_contra hx'
            have m : neg i ∈ S.image neg := Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
            exact (negT i y).1 (hle _ (mem _ (Or.inr m)) ((negT i x).2 hx')) hy'
          have closed : ∀ e ∈ E, e.1 ∈ y \ x ↔ e.2 ∈ y \ x := by
            intro e he
            have k : ∀ z : W, same e z = true ↔ (e.1 ∈ z ↔ e.2 ∈ z) := by
              intro z
              simp only [same, beq_iff_eq]
              rw [Bool.eq_iff_iff, bitT, bitT]
            have s' : (e.1 ∈ x ↔ e.2 ∈ x) ↔ (e.1 ∈ y ↔ e.2 ∈ y) := by
              rw [← k x, ← k y, hsame e he]
            have a := hbit e.1
            have b := hbit e.2
            have m : ∀ i, i ∈ y \ x ↔ i ∈ y ∧ i ∉ x := fun i => Finset.mem_sdiff
            rw [m, m]
            clear k hsame
            tauto
          have inv := (hcomp (y \ x)).1 closed
          have yx : y = x := by
            by_contra hne'
            have : (y \ x).Nonempty := by
              rw [Finset.sdiff_nonempty]
              intro sub
              exact hne' (Finset.Subset.antisymm sub (fun i hi => hbit i hi))
            obtain ⟨i, hi⟩ := this
            have ci : color i = j := by
              by_contra h
              obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
              exact h2 (hS' i h h1)
            have all : ∀ i', color i' = j → i' ∈ y \ x := fun i' h => (inv i i' (ci.trans h.symm)).1 hi
            apply hno
            refine ⟨x, hx, ?_, ?_⟩
            · rw [Finset.disjoint_right]
              intro i' h
              exact (Finset.mem_sdiff.1 (all i' (Finset.mem_filter.1 h).2)).2
            · have : x ∪ K = y := by
                ext i'
                constructor
                · intro h
                  rcases Finset.mem_union.1 h with h | h
                  · exact hbit i' h
                  · exact (Finset.mem_sdiff.1 (all i' (Finset.mem_filter.1 h).2)).1
                · intro h
                  refine Finset.mem_union.2 ?_
                  by_cases hx' : i' ∈ x
                  · exact Or.inl hx'
                  · right
                    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                    by_contra hc'
                    exact hx' (hS' i' hc' h)
              rw [this]; exact hy
          rw [yx]; exact hfx)
        have res := (hk S C.size).1 ⟨C, c1, c2, c3, le_rfl, c4⟩
        obtain ⟨i, hi, hci⟩ := res.1 j
        exact (Finset.mem_filter.1 hi).2 hci
      let first : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.1, bit q.1.1, neg q.1.1] q.2
      let second : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.2, neg q.1.2, bit q.1.2] q.2
      have atomEq : ∀ q x, atom q x = (first q x && second q x) := by
        rintro ⟨e, k⟩ x
        fin_cases k <;> rfl
      let Q := E ×ˢ (Finset.univ : Finset (Fin 3))
      have cardQ : Q.card = 3 * E.card := by simp [Q, mul_comm]
      have noCheap : ∀ q ∈ Q, ∀ g : W → Bool,
          (g ∈ raw ∨ g ∈ Finset.univ.image neg ∨ ∃ q' ∈ Q, q' ≠ q ∧ g = atom q') → ∃ x ∈ A, atom q x ≠ g x := by
        intro q hq g hg
        by_contra hall
        have eqA : ∀ x ∈ A, atom q x = g x := by
          intro x hx
          by_contra h
          exact hall ⟨x, hx, h⟩
        let L := (raw ∪ Finset.univ.image neg).toList
        have mem : ∀ g, g ∈ raw ∨ g ∈ Finset.univ.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
        have negL : ∀ i, neg i ∈ L := fun i => mem _ (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
        have bitL : ∀ i, bit i ∈ L := fun i => mem _ (Or.inl (rawB i))
        have firstL : ∀ q', first q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact bitL _
          · exact negL _
        have secondL : ∀ q', second q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact negL _
          · exact bitL _
        let R := (Q.erase q).toList
        let ps : List (ℕ × ℕ) := R.map (fun q' => (L.idxOf (first q'), L.idxOf (second q')))
        let gates : List PEqualNP.CircuitLowerBounds.Gate := ps.map (fun p => ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.1, p.2]⟩)
        let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
        have psb : ∀ p ∈ ps, p.1 < L.length ∧ p.2 < L.length := by
          intro p hp
          obtain ⟨q', -, rfl⟩ := List.mem_map.1 hp
          exact ⟨List.idxOf_lt_length_iff.2 (firstL q'), List.idxOf_lt_length_iff.2 (secondL q')⟩
        have size : C.size = 3 * E.card - 1 := by
          show gates.length = _
          simp only [gates, ps, R, List.length_map, Finset.length_toList]
          rw [Finset.card_erase_of_mem hq, cardQ]
        have epos : 0 < E.card := Finset.card_pos.2 hne
        have Lpos : 0 < L.length := lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.2 (negL q.1.1))
        have wiresC : ∀ x : W, C.wires (L.map (fun g => g x)) =
            L.map (fun g => g x) ++ ps.map (fun p => (L.map (fun g => g x)).getD p.1 false && (L.map (fun g => g x)).getD p.2 false) := by
          intro x
          refine PEqualNP.Outside.L_meta_53212.and_wires _ ps (fun p hp => ?_)
          rw [List.length_map]
          exact psb p hp
        have atomWire : ∀ q' ∈ Q, q' ≠ q → ∃ j < L.length + C.size, ∀ x : W,
            (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
          intro q' hq' hne'
          have inR : q' ∈ R := Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne', hq'⟩)
          have m := List.idxOf_lt_length_iff.2 inR
          refine ⟨L.length + R.idxOf q', ?_, fun x => ?_⟩
          · have : C.size = R.length := by show gates.length = _; simp [gates, ps]
            omega
          · rw [wiresC, List.getD_append_right _ _ _ _ (by rw [List.length_map]; omega), List.length_map,
              Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD]
            simp only [ps, List.map_map, List.getElem?_map, List.getElem?_eq_getElem m, List.getElem_idxOf, Option.map_some,
              Option.getD_some, Function.comp]
            rw [(PEqualNP.Outside.L_meta_53212.wire_of L _ (firstL q') x).2,
              (PEqualNP.Outside.L_meta_53212.wire_of L _ (secondL q') x).2, atomEq]
        have inputWire : ∀ h ∈ L, ∃ j < L.length + C.size, ∀ x : W, (C.wires (L.map (fun g => g x))).getD j false = h x := by
          intro h hh
          have w := List.idxOf_lt_length_iff.2 hh
          refine ⟨L.idxOf h, by omega, fun x => ?_⟩
          rw [wiresC, List.getD_append _ _ _ _ (by rw [List.length_map]; exact w)]
          exact (PEqualNP.Outside.L_meta_53212.wire_of L h hh x).2
        have res := (hk Finset.univ (3 * E.card - 1)).1 (by
          refine ⟨C, ?_, ?_, ?_, size.le, ?_⟩
          · intro h hh
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
            exact ⟨by simp, by simp⟩
          · intro j hj i hi
            have hj' : j < gates.length := hj
            have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = gates[j] := by
              simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
            rw [e] at hi
            have : gates[j] ∈ gates := List.getElem_mem _
            obtain ⟨p, hp, ep⟩ := List.mem_map.1 this
            rw [← ep] at hi
            simp at hi
            have := psb p hp
            change i < L.length + j
            omega
          · show 0 < L.length + C.size
            omega
          · intro f hfn
            have hfn' := hfn
            simp only [need, Finset.mem_union, Finset.mem_image] at hfn'
            have atomCase : ∀ q' ∈ Q, ∃ j < L.length + C.size, ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
              intro q' hq'
              by_cases h : q' = q
              · subst h
                rcases hg with hg | hg | ⟨q2, hq2, hne2, rfl⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inl hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inr hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := atomWire q2 hq2 hne2
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
              · obtain ⟨j, hj, w⟩ := atomWire q' hq' h
                exact ⟨j, hj, fun x _ => w x⟩
            have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
            rcases hfn' with ((⟨i, -, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
            · obtain ⟨j, hj, w⟩ := inputWire (neg i) (negL i)
              exact ⟨j, hj, fun x _ => w x⟩
            · exact atomCase (e, 0) (inQ e he 0)
            · exact atomCase (e, 1) (inQ e he 1)
            · exact atomCase (e, 2) (inQ e he 2))
        have := res.2
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      have inQ : ∀ i (k : Fin 3), (ed i, k) ∈ Q := fun i k => Finset.mem_product.2 ⟨memE i, Finset.mem_univ _⟩
      have flipsOk : ∀ i, ∃ x ∈ A, ∃ y ∈ A, flip i x y := fun i => by
        obtain ⟨x, hx, d, u⟩ := flips i
        exact ⟨x, hx, x ∪ Kc i, u, toFlip i x (x ∪ Kc i) d (by congr)⟩
      refine ⟨⟨?_, ?_, ?_, ?_⟩, flipsOk⟩
      · intro a b h
        by_contra hne'
        have q : (ed a.1, kv a.2) ≠ (ed b.1, kv b.2) := by
          intro e
          obtain ⟨e1, e2⟩ := Prod.mk.inj e
          exact hne' (Prod.ext (edInj e1) (kvInj _ _ e2))
        obtain ⟨x, hx, d⟩ := noCheap _ (inQ a.1 (kv a.2)) (atom (ed b.1, kv b.2))
          (Or.inr (Or.inr ⟨_, inQ b.1 (kv b.2), q.symm, rfl⟩))
        apply d
        have h' : G (A.image pat) a = G (A.image pat) b := h
        rw [Bool.eq_iff_iff, ← fP a x hx, ← fP b x hx, h']
      · intro a
        obtain ⟨x, hx, d⟩ := noCheap _ (inQ a.1 (kv a.2)) _ (Or.inl rawF)
        have t : atom (ed a.1, kv a.2) x = true := by
          have : atom (ed a.1, kv a.2) x ≠ false := d
          simpa using this
        exact ⟨pat x, (fP a x hx).2 t⟩
      · intro i
        obtain ⟨x, hx, y, -, f⟩ := flipsOk i
        exact ⟨pat x, PEqualNP.Outside.L_meta_53212.memI hx,
          (pat0 x i).2 (iff_of_false f.1 f.2.1)⟩
      · intro a i
        show G (A.image pat) a ≠ G (A.image pat) (i, false) ∪ G (A.image pat) (i, true) ∧
          G (A.image pat) a ≠ A.image pat \ (G (A.image pat) (i, false) ∪ G (A.image pat) (i, true))
        have inU : ∀ x ∈ A, (pat x ∈ G (A.image pat) (i, false) ∪ G (A.image pat) (i, true) ↔ pat x i ≠ 0) := by
          intro x hx
          rw [PEqualNP.Outside.L_meta_53212.memU', mG, mG]
          have inP : pat x ∈ A.image pat := PEqualNP.Outside.L_meta_53212.memI hx
          simp only [inP, true_and]
          constructor
          · rintro (h | h)
            · rw [h]; exact kv0 false
            · rw [h]; exact kv0 true
          · intro h
            obtain ⟨s, hs⟩ := kOf _ h
            cases s
            · exact Or.inl hs
            · exact Or.inr hs
        have sameP : ∀ x : W, same (ed i) x = true ↔ pat x i = 0 := fun x => by
          rw [sameT, pat0]
        constructor
        · intro h
          obtain ⟨x, hx, d⟩ := noCheap _ (inQ a.1 (kv a.2)) (fun x => !(same (ed i) x)) (Or.inl (rawD _ (memE i)))
          apply d
          show atom (ed a.1, kv a.2) x = !(same (ed i) x)
          rw [Bool.eq_iff_iff, ← fP a x hx, Bool.not_eq_true', ← Bool.not_eq_true, sameP, ← ne_eq, ← inU x hx]
          rw [h]
        · intro h
          obtain ⟨x, hx, d⟩ := noCheap _ (inQ a.1 (kv a.2)) (same (ed i)) (Or.inl (rawS _ (memE i)))
          apply d
          rw [Bool.eq_iff_iff, ← fP a x hx, sameP, h, PEqualNP.Outside.L_meta_53212.memSd, inU x hx, not_not]
          exact and_iff_right (PEqualNP.Outside.L_meta_53212.memI hx)
    · rintro ⟨⟨finj, fne, fzero, fno⟩, fl⟩ S p
      intro L
      have ex : ∀ i, ∃ x : W, x ∈ A ∧ (x ∪ Kc i : Finset (Fin n)) ∈ (A : Finset (Finset (Fin n))) ∧ Disjoint (x : Finset (Fin n)) (Kc i) := by
        intro i
        obtain ⟨x, hx, y, hy, f⟩ := fl i
        obtain ⟨d, e⟩ := flipEq i x y f
        exact ⟨x, hx, e ▸ hy, d⟩
      choose X hX hY hdis using ex
      let Y : Fin m → W := fun i => (X i : Finset (Fin n)) ∪ Kc i
      have hYA : ∀ i, Y i ∈ A := hY
      have inL : ∀ g, g ∈ raw ∨ g ∈ S.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
      have ofL : ∀ g ∈ L, g ∈ raw ∨ ∃ s ∈ S, neg s = g := fun g hg =>
        (Finset.mem_union.1 (Finset.mem_toList.1 hg)).imp id Finset.mem_image.1
      have needNeg : ∀ v, neg v ∈ need := fun v =>
        Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
          (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
      have needAtom : ∀ e ∈ E, ∀ k, atom (e, k) ∈ need := by
        intro e he k
        fin_cases k
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))))
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
        · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
      let Eq' : (W → Bool) → (W → Bool) → Prop := fun f g => ∀ x ∈ A, f x = g x
      have wX : ∀ i w, color w = i → w ∉ (X i : Finset (Fin n)) := fun i w h hx =>
        Finset.disjoint_left.1 (hdis i) hx ((mK i w).2 h)
      have wY : ∀ i w, color w = i → w ∈ (Y i : Finset (Fin n)) := fun i w h =>
        Finset.mem_union.2 (Or.inr ((mK i w).2 h))
      have wO : ∀ i w, color w ≠ i → (w ∈ (Y i : Finset (Fin n)) ↔ w ∈ (X i : Finset (Fin n))) := fun i w h =>
        ⟨fun hy => (Finset.mem_union.1 hy).resolve_right (fun k => h ((mK i w).1 k)), fun hx => Finset.mem_union.2 (Or.inl hx)⟩
      have bitX : ∀ i w, color w = i → bit w (X i) = false := fun i w h => by
        rw [← Bool.not_eq_true, bitT]; exact wX i w h
      have bitY : ∀ i w, color w = i → bit w (Y i) = true := fun i w h => (bitT _ _).2 (wY i w h)
      have bitO : ∀ i w, color w ≠ i → bit w (Y i) = bit w (X i) := fun i w h => by
        rw [Bool.eq_iff_iff, bitT, bitT]; exact wO i w h
      have negX : ∀ i w, color w = i → neg w (X i) = true := fun i w h => by
        show (!(bit w (X i))) = true; rw [bitX i w h]; rfl
      have negY : ∀ i w, color w = i → neg w (Y i) = false := fun i w h => by
        show (!(bit w (Y i))) = false; rw [bitY i w h]; rfl
      have negO : ∀ i w, color w ≠ i → neg w (Y i) = neg w (X i) := fun i w h => by
        show (!(bit w (Y i))) = !(bit w (X i)); rw [bitO i w h]
      have sameInv : ∀ i j, same (ed j) (Y i) = same (ed j) (X i) := by
        intro i j
        rw [Bool.eq_iff_iff, sameT, sameT]
        show (U j ∈ (Y i : Finset (Fin n)) ↔ V j ∈ (Y i : Finset (Fin n))) ↔
          (U j ∈ (X i : Finset (Fin n)) ↔ V j ∈ (X i : Finset (Fin n)))
        by_cases h : j = i
        · exact iff_of_true (iff_of_true (wY i _ (by rw [colU, h])) (wY i _ (by rw [colV, h])))
            (iff_of_false (wX i _ (by rw [colU, h])) (wX i _ (by rw [colV, h])))
        · exact iff_congr (wO i _ (by rw [colU]; exact h)) (wO i _ (by rw [colV]; exact h))
      have atomInv : ∀ i j (k : Fin 3), (k ≠ 0 ∨ j ≠ i) → atom (ed j, k) (Y i) = atom (ed j, k) (X i) := by
        intro i j k h
        by_cases hj : j = i
        · have hk : k ≠ 0 := h.resolve_right (not_not.2 hj)
          obtain ⟨s, rfl⟩ := kOf k hk
          have fa : atom (ed j, kv s) (Y i) = false := by
            rw [← Bool.not_eq_true, atomPat]
            rw [(pat0 (Y i) j).2 (iff_of_true (wY i _ (by rw [colU, hj])) (wY i _ (by rw [colV, hj])))]
            exact fun h => kv0 s h.symm
          have fb : atom (ed j, kv s) (X i) = false := by
            rw [← Bool.not_eq_true, atomPat]
            rw [(pat0 (X i) j).2 (iff_of_false (wX i _ (by rw [colU, hj])) (wX i _ (by rw [colV, hj])))]
            exact fun h => kv0 s h.symm
          rw [fa, fb]
        · have n1 := negO i (U j) (by rw [colU]; exact hj)
          have n2 := negO i (V j) (by rw [colV]; exact hj)
          have b1 := bitO i (U j) (by rw [colU]; exact hj)
          have b2 := bitO i (V j) (by rw [colV]; exact hj)
          fin_cases k
          · show (neg (U j) (Y i) && neg (V j) (Y i)) = (neg (U j) (X i) && neg (V j) (X i))
            rw [n1, n2]
          · show (bit (U j) (Y i) && neg (V j) (Y i)) = (bit (U j) (X i) && neg (V j) (X i))
            rw [b1, n2]
          · show (neg (U j) (Y i) && bit (V j) (Y i)) = (neg (U j) (X i) && bit (V j) (X i))
            rw [n1, b2]
      have a0X : ∀ i, atom (ed i, 0) (X i) = true := fun i =>
        (a0 _ _).2 ⟨wX i _ (colU i), wX i _ (colV i)⟩
      have a0Y : ∀ i, atom (ed i, 0) (Y i) = false := fun i => by
        rw [← Bool.not_eq_true, a0]
        exact fun h => h.1 (wY i _ (colU i))
      -- una funcion que cambia al voltear no puede igualar a una que no cambia
      have moves : ∀ (f g : W → Bool) i, Eq' f g → f (X i) ≠ f (Y i) → g (Y i) = g (X i) → False := by
        intro f g i h hf hg
        exact hf (by rw [h _ (hX i), h _ (hYA i), hg])
      have patRow : ∀ i s, ∃ x ∈ A, pat x i = kv s := by
        intro i s
        obtain ⟨z, hz⟩ := fne (i, s)
        have hz' := (mG (A.image pat) (i, s) z).1 hz
        obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' hz'.1
        exact ⟨x, hx, hz'.2⟩
      have negneg : ∀ v w, Eq' (neg v) (neg w) → v = w := by
        intro v w he
        by_contra hne'
        by_cases hc : color v = color w
        · obtain ⟨x, hx, hp⟩ := patRow (color v) false
          have p := (pat1 x _).1 (hp.trans kvF)
          have q := he x hx
          rw [Bool.eq_iff_iff, negT, negT] at q
          rcases cases_ v with ev | ev <;> rcases cases_ w with ew | ew <;> rw [← hc] at ew
          · exact hne' (ev.trans ew.symm)
          · rw [← ev] at p; rw [← ew] at p
            exact (q.2 p.2) p.1
          · rw [← ew] at p; rw [← ev] at p
            exact (q.1 p.2) p.1
          · exact hne' (ev.trans ew.symm)
        · refine moves _ _ (color v) he (by rw [negX _ v rfl, negY _ v rfl]; decide) (negO _ w (Ne.symm hc))
      have negAtom : ∀ v, ∀ e ∈ E, ∀ k, ¬ Eq' (neg v) (atom (e, k)) := by
        intro v e he k heq
        obtain ⟨j, rfl⟩ := ofE e he
        by_cases h : k ≠ 0 ∨ j ≠ color v
        · exact moves _ _ (color v) heq (by rw [negX _ v rfl, negY _ v rfl]; decide) (atomInv _ _ _ h)
        · rw [not_or, not_not, not_not] at h
          obtain ⟨k0, hj⟩ := h
          subst k0
          rcases cases_ v with ev | ev <;> rw [← hj] at ev
          · obtain ⟨x, hx, hp⟩ := patRow j true
            have p := (pat2 x j).1 (hp.trans kvT)
            have q := heq x hx
            rw [Bool.eq_iff_iff, negT, a0] at q
            exact (q.1 (ev ▸ p.1)).2 p.2
          · obtain ⟨x, hx, hp⟩ := patRow j false
            have p := (pat1 x j).1 (hp.trans kvF)
            have q := heq x hx
            rw [Bool.eq_iff_iff, negT, a0] at q
            exact (q.1 (ev ▸ p.2)).1 p.1
      have negRaw : ∀ v, ∀ g ∈ raw, ¬ Eq' (neg v) g := by
        intro v g hg heq
        have mv : neg v (X (color v)) ≠ neg v (Y (color v)) := by rw [negX _ v rfl, negY _ v rfl]; decide
        rcases Finset.mem_union.1 hg with hg | hg
        · rcases Finset.mem_union.1 hg with hg | hg
          · rcases Finset.mem_union.1 hg with hg | hg
            · rcases Finset.mem_insert.1 hg with h | h
              · exact moves _ _ _ heq mv (by rw [h])
              · exact moves _ _ _ heq mv (by rw [Finset.mem_singleton.1 h])
            · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hg
              by_cases hc : color w = color v
              · have q := heq _ (hX (color v))
                rw [negX _ v rfl, bitX _ w hc] at q
                exact Bool.noConfusion q
              · exact moves _ _ _ heq mv (bitO _ w hc)
          · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
            obtain ⟨j, rfl⟩ := ofE e he
            exact moves _ _ _ heq mv (sameInv _ _)
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
          obtain ⟨j, rfl⟩ := ofE e he
          exact moves _ _ _ heq mv (by show (!(same (ed j) (Y (color v)))) = !(same (ed j) (X (color v))); rw [sameInv])
      have atomRaw : ∀ e ∈ E, ∀ k, ∀ g, g ∈ raw ∨ (∃ i, g = neg i) → ¬ Eq' (atom (e, k)) g := by
        intro e he k g hg heq
        rcases hg with hg | ⟨w, rfl⟩
        swap
        · exact negAtom w e he k (fun x hx => (heq x hx).symm)
        obtain ⟨j, rfl⟩ := ofE e he
        have mv0 : atom (ed j, 0) (X j) ≠ atom (ed j, 0) (Y j) := by rw [a0X, a0Y]; decide
        have xk : ∀ s, atom (ed j, kv s) (X j) = false := fun s => by
          rw [← Bool.not_eq_true, atomPat, (pat0 (X j) j).2 (iff_of_false (wX j _ (colU j)) (wX j _ (colV j)))]
          exact fun h => kv0 s h.symm
        rcases Finset.mem_union.1 hg with hg | hg
        · rcases Finset.mem_union.1 hg with hg | hg
          · rcases Finset.mem_union.1 hg with hg | hg
            · by_cases hk : k = 0
              · subst hk
                rcases Finset.mem_insert.1 hg with h | h
                · exact moves _ _ _ heq mv0 (by rw [h])
                · exact moves _ _ _ heq mv0 (by rw [Finset.mem_singleton.1 h])
              obtain ⟨s, rfl⟩ := kOf k hk
              rcases Finset.mem_insert.1 hg with h | h
              · obtain ⟨x, hx, hp⟩ := patRow j s
                have q := heq x hx
                rw [h, (atomPat j s x).2 hp] at q
                exact Bool.noConfusion q
              · have q := heq _ (hX j)
                rw [Finset.mem_singleton.1 h, xk] at q
                exact Bool.noConfusion q
            · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hg
              by_cases hk : k = 0
              · subst hk
                by_cases hc : color w = j
                · have q := heq _ (hX j)
                  rw [a0X, bitX _ w hc] at q
                  exact Bool.noConfusion q
                · exact moves _ _ _ heq mv0 (bitO _ w hc)
              by_cases hc : color w = j
              · obtain ⟨s, rfl⟩ := kOf k hk
                have q := heq _ (hYA j)
                have z : atom (ed j, kv s) (Y j) = false := by
                  rw [atomInv j j _ (Or.inl (kv0 s)), xk]
                rw [z, bitY _ w hc] at q
                exact Bool.noConfusion q
              · refine moves _ _ (color w) (fun x hx => (heq x hx).symm)
                  (by rw [bitX _ w rfl, bitY _ w rfl]; decide) (atomInv _ _ _ (Or.inl hk))
          · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
            obtain ⟨i, rfl⟩ := ofE f hf
            by_cases hk : k = 0
            · subst hk
              exact moves _ _ _ heq mv0 (sameInv _ _)
            obtain ⟨s, rfl⟩ := kOf k hk
            have no : G (A.image pat) (j, s) ≠ A.image pat \ (G (A.image pat) (i, false) ∪ G (A.image pat) (i, true)) :=
              (fno (j, s) i).2
            apply no
            ext z
            rw [PEqualNP.Outside.L_meta_53212.memSd, PEqualNP.Outside.L_meta_53212.memU', mG, mG, mG]
            constructor
            · rintro ⟨zP, zj⟩
              obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' zP
              refine ⟨zP, fun hu => ?_⟩
              have s1 : same (ed i) x = true := by
                exact (heq x hx).symm.trans ((atomPat j s x).2 zj)
              rw [sameT] at s1
              have p0 := (pat0 x i).2 s1
              rcases hu with h | h
              · exact kv0 false (h.2.symm.trans p0)
              · exact kv0 true (h.2.symm.trans p0)
            · rintro ⟨zP, hz⟩
              obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' zP
              have p0 : pat x i = 0 := by
                by_contra h
                obtain ⟨t, ht⟩ := kOf _ h
                apply hz
                cases t
                · exact Or.inl ⟨zP, ht⟩
                · exact Or.inr ⟨zP, ht⟩
              have s1 : same (ed i) x = true := (sameT _ _).2 ((pat0 x i).1 p0)
              refine ⟨zP, (atomPat j s x).1 ?_⟩
              exact (heq x hx).trans s1
        · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
          obtain ⟨i, rfl⟩ := ofE f hf
          by_cases hk : k = 0
          · subst hk
            exact moves _ _ _ heq mv0 (by show (!(same (ed i) (Y j))) = !(same (ed i) (X j)); rw [sameInv])
          obtain ⟨s, rfl⟩ := kOf k hk
          have no : G (A.image pat) (j, s) ≠ G (A.image pat) (i, false) ∪ G (A.image pat) (i, true) :=
            (fno (j, s) i).1
          apply no
          ext z
          rw [PEqualNP.Outside.L_meta_53212.memU', mG, mG, mG]
          constructor
          · rintro ⟨zP, zj⟩
            obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' zP
            have d1 : (!(same (ed i) x)) = true := by
              exact (heq x hx).symm.trans ((atomPat j s x).2 zj)
            have p0 : pat x i ≠ 0 := by
              intro h
              have s1 : same (ed i) x = true := (sameT _ _).2 ((pat0 x i).1 h)
              rw [s1] at d1
              exact Bool.noConfusion d1
            obtain ⟨t, ht⟩ := kOf _ p0
            cases t
            · exact Or.inl ⟨zP, ht⟩
            · exact Or.inr ⟨zP, ht⟩
          · intro hz
            have h : (z ∈ A.image pat ∧ z i ≠ 0) := by
              rcases hz with ⟨zP, e⟩ | ⟨zP, e⟩
              · exact ⟨zP, by rw [e]; exact kv0 false⟩
              · exact ⟨zP, by rw [e]; exact kv0 true⟩
            obtain ⟨zP, p0⟩ := h
            obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' zP
            have d1 : (!(same (ed i) x)) = true := by
              rw [Bool.not_eq_true', ← Bool.not_eq_true, sameT, ← pat0]
              exact p0
            refine ⟨zP, (atomPat j s x).1 ?_⟩
            exact (heq x hx).trans d1
      have atomAtom : ∀ e ∈ E, ∀ e' ∈ E, ∀ k k', Eq' (atom (e, k)) (atom (e', k')) → (e, k) = (e', k') := by
        intro e he e' he' k k' heq
        obtain ⟨j, rfl⟩ := ofE e he
        obtain ⟨j', rfl⟩ := ofE e' he'
        have mv : ∀ i, atom (ed i, 0) (X i) ≠ atom (ed i, 0) (Y i) := fun i => by rw [a0X, a0Y]; decide
        by_cases hk : k = 0
        · subst hk
          by_cases h : k' ≠ 0 ∨ j' ≠ j
          · exact (moves _ _ j heq (mv j) (atomInv _ _ _ h)).elim
          · rw [not_or, not_not, not_not] at h
            rw [h.1, h.2]
        by_cases hk' : k' = 0
        · subst hk'
          exact (moves _ _ j' (fun x hx => (heq x hx).symm) (mv j') (atomInv _ _ _ (Or.inl hk))).elim
        obtain ⟨s, rfl⟩ := kOf k hk
        obtain ⟨s', rfl⟩ := kOf k' hk'
        have : (j, s) = (j', s') := by
          refine finj ?_
          show G (A.image pat) (j, s) = G (A.image pat) (j', s')
          ext z
          rw [mG, mG]
          refine and_congr_right (fun zP => ?_)
          obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' zP
          rw [← atomPat, ← atomPat, heq x hx]
        obtain ⟨e1, e2⟩ := Prod.mk.inj this
        rw [e1, e2]
      constructor
      · rintro ⟨C, mono, -, -, size, comp⟩
        refine (cond S p).2 ?_
        have meets : ∀ j : Fin c, ∃ i ∈ S, color i = j := by
          intro j
          by_contra hno
          obtain ⟨v, hv⟩ := hsurj j
          obtain ⟨w, -, hw⟩ := comp (neg v) (needNeg v)
          have r0 := hw _ (hX j)
          have r1 := hw _ (hYA j)
          rw [negX j v hv] at r0
          rw [negY j v hv] at r1
          have up : ∀ i, (L.map (fun g : W → Bool => g (X j))).getD i false = true →
              (L.map (fun g : W → Bool => g (Y j))).getD i false = true := by
            intro i hi
            by_cases hlt : i < L.length
            swap
            · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega)] at hi
              exact Bool.noConfusion hi
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt] at hi ⊢
            change L[i] (X j) = true at hi
            change L[i] (Y j) = true
            rcases ofL _ (List.getElem_mem hlt) with hg | ⟨s, hs, e⟩
            · rcases Finset.mem_union.1 hg with hg | hg
              · rcases Finset.mem_union.1 hg with hg | hg
                · rcases Finset.mem_union.1 hg with hg | hg
                  · rcases Finset.mem_insert.1 hg with e | hg
                    · rw [e] at hi; exact Bool.noConfusion hi
                    · rw [Finset.mem_singleton.1 hg]
                  · obtain ⟨i', -, e⟩ := Finset.mem_image.1 hg
                    rw [← e] at hi ⊢
                    exact (bitT _ _).2 (Finset.mem_union.2 (Or.inl ((bitT _ _).1 hi)))
                · obtain ⟨f, hf, e⟩ := Finset.mem_image.1 hg
                  obtain ⟨q, rfl⟩ := ofE f hf
                  rw [← e] at hi ⊢
                  rw [sameInv]; exact hi
              · obtain ⟨f, hf, e⟩ := Finset.mem_image.1 hg
                obtain ⟨q, rfl⟩ := ofE f hf
                rw [← e] at hi ⊢
                show (!(same (ed q) (Y j))) = true
                rw [sameInv]; exact hi
            · rw [← e] at hi ⊢
              have : color s ≠ j := fun h => hno ⟨s, hs, h⟩
              rw [negO j s this]; exact hi
          have gk : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
            fun g hg => by simpa using (mono g hg).1
          have := PEqualNP.Outside.L_meta_53212.circuit_mono C.gates gk
            (L.map (fun g : W → Bool => g (X j))) (L.map (fun g : W → Bool => g (Y j)))
            (by rw [List.length_map, List.length_map]) up w r0
          have h3 : (C.wires (L.map (fun g : W → Bool => g (Y j)))).getD w false = true := this
          rw [r1] at h3
          exact Bool.noConfusion h3
        refine ⟨meets, ?_⟩
        let N : Finset (Fin n ⊕ ((Fin n × Fin n) × Fin 3)) := (Sᶜ).disjSum (E ×ˢ (Finset.univ : Finset (Fin 3)))
        let fn : Fin n ⊕ ((Fin n × Fin n) × Fin 3) → (W → Bool) := Sum.elim neg atom
        have fnNeed : ∀ q ∈ N, fn q ∈ need := by
          rintro (v | ⟨e, k⟩) hq
          · exact needNeg v
          · exact needAtom e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 k
        have notInput : ∀ q ∈ N, ∀ g ∈ L, ¬ Eq' (fn q) g := by
          rintro (v | ⟨e, k⟩) hq g hg heq
          · have vS : v ∉ S := Finset.mem_compl.1 (Finset.inl_mem_disjSum.1 hq)
            rcases ofL g hg with h | ⟨s, hs, rfl⟩
            · exact negRaw v g h heq
            · exact vS ((negneg v s heq) ▸ hs)
          · have he := (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1
            rcases ofL g hg with h | ⟨s, -, rfl⟩
            · exact atomRaw e he k g (Or.inl h) heq
            · exact atomRaw e he k _ (Or.inr ⟨s, rfl⟩) heq
        have distinct : ∀ q ∈ N, ∀ q' ∈ N, Eq' (fn q) (fn q') → q = q' := by
          rintro (v | ⟨e, k⟩) hq (w | ⟨e', k'⟩) hq' heq
          · rw [negneg v w heq]
          · exact absurd heq (negAtom v e' (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq')).1 k')
          · exact absurd (fun x hx => (heq x hx).symm)
              (negAtom w e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 k)
          · rw [atomAtom e (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq)).1 e'
              (Finset.mem_product.1 (Finset.inr_mem_disjSum.1 hq')).1 k k' heq]
        have wire : ∀ q : ↥N, ∃ j, j < L.length + C.size ∧ ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = fn q.1 x :=
          fun q => comp _ (fnNeed q.1 q.2)
        choose wj hlt hval using wire
        have high : ∀ q, L.length ≤ wj q := by
          intro q
          by_contra hc
          have hc' : wj q < L.length := not_le.1 hc
          refine notInput q.1 q.2 (L[wj q]) (List.getElem_mem hc') (fun x hx => ?_)
          rw [← hval q x hx]
          have := PEqualNP.Outside.L_meta_53212.val_input (L.map (fun g => g x)) C.gates (wj q) (by rw [List.length_map]; exact hc')
          change (C.wires (L.map (fun g => g x))).getD (wj q) false = _ at this
          rw [this, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc']
          rfl
        let slot : ↥N → Fin C.size := fun q => ⟨wj q - L.length, by have := hlt q; have := high q; omega⟩
        have inj : Function.Injective slot := by
          intro q q' e
          have e' : wj q = wj q' := by
            have := congrArg Fin.val e
            have h1 := high q
            have h2 := high q'
            simp only [slot] at this
            omega
          exact Subtype.ext (distinct q.1 q.2 q'.1 q'.2 (fun x hx => by rw [← hval q x hx, ← hval q' x hx, e']))
        have count := Fintype.card_le_of_injective slot inj
        rw [Fintype.card_coe, Fintype.card_fin] at count
        have cardN : N.card = (n - S.card) + 3 * E.card := by
          simp only [N, Finset.card_disjSum, Finset.card_product, Finset.card_univ, Fintype.card_fin]
          rw [Finset.card_compl, Fintype.card_fin]
          ring
        have : S.card ≤ n := by simpa using Finset.card_le_univ S
        omega
      · intro h
        exact build A S p ((cond S p).1 h)
  refine ⟨equiv, fun P b => ?_⟩
  constructor
  · rintro ⟨A, rfl, hk, hb⟩
    obtain ⟨adm, fl⟩ := (equiv A).1 hk
    refine ⟨adm, le_trans ?_ hb⟩
    have ex : ∀ i, ∃ x : W, x ∈ A ∧ (x ∪ Kc i : Finset (Fin n)) ∈ (A : Finset (Finset (Fin n))) ∧ Disjoint (x : Finset (Fin n)) (Kc i) := by
      intro i
      obtain ⟨x, hx, y, hy, f⟩ := fl i
      refine ⟨x, hx, ?_, ?_⟩
      · have : (y : Finset (Fin n)) = (x : Finset (Fin n)) ∪ Kc i := by
          obtain ⟨h1, h2, h3⟩ := f
          ext w
          have e3 : (y : Finset (Fin n)) = insert (U i) (insert (V i) (x : Finset (Fin n))) := by
            rw [h3]; ext v; exact (PEqualNP.Outside.L_meta_53212.memIns.trans (or_congr_right PEqualNP.Outside.L_meta_53212.memIns)).trans (PEqualNP.Outside.L_meta_53212.memIns.trans (or_congr_right PEqualNP.Outside.L_meta_53212.memIns)).symm
          rw [e3, Finset.mem_union, mK]
          refine (PEqualNP.Outside.L_meta_53212.memIns.trans (or_congr_right PEqualNP.Outside.L_meta_53212.memIns)).trans ?_
          constructor
          · rintro (h | h | h)
            · exact Or.inr (by rw [h, colU])
            · exact Or.inr (by rw [h, colV])
            · exact Or.inl h
          · rintro (h | h)
            · exact Or.inr (Or.inr h)
            · rcases cases_ w with e | e
              · rw [h] at e; exact Or.inl e
              · rw [h] at e; exact Or.inr (Or.inl e)
        exact this ▸ hy
      · rw [Finset.disjoint_right]
        intro w hw
        have cw := (mK i w).1 hw
        rcases cases_ w with e | e
        · rw [cw] at e; rw [e]; exact f.1
        · rw [cw] at e; rw [e]; exact f.2.1
    choose X hX hY hdis using ex
    have xj_ : True := trivial
    let xj : Fin c → Finset (Fin n) := X
    have hxj : ∀ j, xj j ∈ (A : Finset (Finset (Fin n))) := hX
    have hflip : ∀ j, xj j ∪ Kc j ∈ (A : Finset (Finset (Fin n))) := hY
    let K := Kc
    let Rel : Finset (Fin c) → ↥(A : Finset (Finset (Fin n))) → ↥(A : Finset (Finset (Fin n))) → Prop :=
      fun J a b => ∃ j ∈ J, a.1 = xj j ∧ b.1 = xj j ∪ K j
    let ψ : Finset (Fin c) → Finset (Fin n) → Finset (Fin n) := fun J x => x.filter (fun i => color i ∉ J)
    have psiInv : ∀ J a b, Rel J a b → ψ J a.1 = ψ J b.1 := by
      rintro J a b ⟨j, hj, h1, h2⟩
      rw [h1, h2]
      ext i
      show i ∈ (xj j).filter (fun i => color i ∉ J) ↔ i ∈ (xj j ∪ K j).filter (fun i => color i ∉ J)
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨h, hc'⟩; exact ⟨Finset.mem_union.2 (Or.inl h), hc'⟩
      · rintro ⟨h, hc'⟩
        rcases Finset.mem_union.1 h with h | h
        · exact ⟨h, hc'⟩
        · exact absurd (((mK _ _).1 h).symm ▸ hj) hc'
    have count : ∀ J : Finset (Fin c), Nat.card (Quot (Rel J)) + J.card ≤ A.card := by
      intro J
      induction J using Finset.induction with
      | empty =>
        have : Nat.card (Quot (Rel ∅)) ≤ Nat.card ↥(A : Finset (Finset (Fin n))) :=
          Nat.card_le_card_of_surjective (Quot.mk (Rel ∅)) Quot.mk_surjective
        simpa using this
      | insert k J hkJ ih =>
        let φ : Quot (Rel J) → Quot (Rel (insert k J)) :=
          Quot.map id (fun a b ⟨j, hj, h⟩ => ⟨j, Finset.mem_insert_of_mem hj, h⟩)
        have surj : Function.Surjective φ := by
          intro q
          obtain ⟨a, rfl⟩ := Quot.mk_surjective q
          exact ⟨Quot.mk _ a, rfl⟩
        have notinj : ¬ Function.Injective φ := by
          intro inj
          let a : ↥(A : Finset (Finset (Fin n))) := ⟨xj k, hxj k⟩
          let b : ↥(A : Finset (Finset (Fin n))) := ⟨xj k ∪ K k, hflip k⟩
          have e : φ (Quot.mk _ a) = φ (Quot.mk _ b) :=
            Quot.sound ⟨k, Finset.mem_insert_self _ _, rfl, rfl⟩
          have e' := inj e
          have := congrArg (Quot.lift (fun a : ↥(A : Finset (Finset (Fin n))) => ψ J a.1) (psiInv J)) e'
          change ψ J (xj k) = ψ J (xj k ∪ K k) at this
          obtain ⟨i, hi⟩ := hsurj k
          have h2 : i ∈ ψ J (xj k ∪ K k) := by
            refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩), ?_⟩
            rw [hi]; exact hkJ
          rw [← this] at h2
          exact Finset.disjoint_left.1 (hdis k) (Finset.mem_filter.1 h2).1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        have fin1 : Finite (Quot (Rel J)) := Finite.of_surjective _ Quot.mk_surjective
        have fin2 : Finite (Quot (Rel (insert k J))) := Finite.of_surjective _ Quot.mk_surjective
        have lt : Nat.card (Quot (Rel (insert k J))) < Nat.card (Quot (Rel J)) := by
          have i1 := Fintype.ofFinite (Quot (Rel J))
          have i2 := Fintype.ofFinite (Quot (Rel (insert k J)))
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Fintype.card_lt_of_surjective_not_injective φ surj notinj
        rw [Finset.card_insert_of_notMem hkJ]
        omega
    have total := count Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at total
    have patInv : ∀ a b : ↥(A : Finset (Finset (Fin n))), Rel Finset.univ a b → pat a.1 = pat b.1 := by
      rintro a b ⟨j, -, h1, h2⟩
      funext i
      have key : ∀ x : Finset (Fin n), Disjoint x (Kc j) → pat x i = pat (x ∪ Kc j : Finset (Fin n)) i := by
        intro x hd
        by_cases h : i = j
        · have p1 : pat x i = 0 := (pat0 x i).2 (iff_of_false
            (fun k => Finset.disjoint_left.1 hd k ((mK _ _).2 (by rw [colU, h])))
            (fun k => Finset.disjoint_left.1 hd k ((mK _ _).2 (by rw [colV, h]))))
          have p2 : pat (x ∪ Kc j : Finset (Fin n)) i = 0 := (pat0 _ i).2 (iff_of_true
            (Finset.mem_union.2 (Or.inr ((mK _ _).2 (by rw [colU, h]))))
            (Finset.mem_union.2 (Or.inr ((mK _ _).2 (by rw [colV, h])))))
          rw [p1, p2]
        · have o : ∀ w, color w = i → (bit w x = bit w (x ∪ Kc j : Finset (Fin n))) := by
            intro w hw
            rw [Bool.eq_iff_iff, bitT, bitT]
            exact ⟨fun k => Finset.mem_union.2 (Or.inl k),
              fun k => (Finset.mem_union.1 k).resolve_right (fun l => h (hw.symm.trans ((mK _ _).1 l)))⟩
          rw [patG x i _ _ rfl rfl, patG (x ∪ Kc j : Finset (Fin n)) i _ _ rfl rfl, o (U i) (colU i), o (V i) (colV i)]
      rw [h1, h2]
      exact key (xj j) (hdis j)
    have fin1 : Finite (Quot (Rel Finset.univ)) := Finite.of_surjective _ Quot.mk_surjective
    have le : (A.image pat).card ≤ Nat.card (Quot (Rel Finset.univ)) := by
      have i1 := Fintype.ofFinite (Quot (Rel Finset.univ))
      rw [Nat.card_eq_fintype_card]
      have sub : A.image pat ⊆ Finset.univ.image (Quot.lift (fun a : ↥(A : Finset (Finset (Fin n))) => pat a.1) patInv) := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := PEqualNP.Outside.L_meta_53212.memI'' hz
        exact PEqualNP.Outside.L_meta_53212.memI (f := Quot.lift (fun a : ↥(A : Finset (Finset (Fin n))) => pat a.1) patInv)
          (a := Quot.mk _ ⟨x, hx⟩) (Finset.mem_univ _)
      exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (le_of_eq Finset.card_univ))
    have cA : (A : Finset (Finset (Fin n))).card = A.card := rfl
    omega
  · rintro ⟨⟨finj, fne, fzero, fno⟩, hb⟩
    let rep : K0 → Finset (Fin n) := fun z => Finset.univ.filter
      (fun w => (z (color w) = 1 ∧ w = U (color w)) ∨ (z (color w) = 2 ∧ w = V (color w)))
    have mrep : ∀ z w, w ∈ rep z ↔ (z (color w) = 1 ∧ w = U (color w)) ∨ (z (color w) = 2 ∧ w = V (color w)) := fun z w => by
      rw [PEqualNP.Outside.L_meta_53212.memF]
      exact and_iff_right (Finset.mem_univ _)
    have repU : ∀ z i, U i ∈ rep z ↔ z i = 1 := by
      intro z i
      rw [mrep, colU]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact absurd h.2 (UV i)
      · intro h; exact Or.inl ⟨h, rfl⟩
    have repV : ∀ z i, V i ∈ rep z ↔ z i = 2 := by
      intro z i
      rw [mrep, colV]
      constructor
      · rintro (h | h)
        · exact absurd h.2.symm (UV i)
        · exact h.1
      · intro h; exact Or.inr ⟨h, rfl⟩
    have three : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    have patRep : ∀ z, pat (rep z) = z := by
      intro z
      funext i
      rcases three (z i) with h | h | h
      · rw [h]
        refine (pat0 (rep z) i).2 (iff_of_false (fun k => ?_) (fun k => ?_))
        · rw [repU, h] at k; exact absurd k (by decide)
        · rw [repV, h] at k; exact absurd k (by decide)
      · rw [h]
        refine (pat1 (rep z) i).2 ⟨(repU z i).2 h, fun k => ?_⟩
        rw [repV, h] at k; exact absurd k (by decide)
      · rw [h]
        refine (pat2 (rep z) i).2 ⟨fun k => ?_, (repV z i).2 h⟩
        rw [repU, h] at k; exact absurd k (by decide)
    choose zi hzi hz0 using fzero
    have dis : ∀ i, Disjoint (rep (zi i)) (Kc i) := by
      intro i
      rw [Finset.disjoint_right]
      intro w hw k
      have cw := (mK i w).1 hw
      rw [mrep, cw, hz0] at k
      rcases k with k | k <;> exact absurd k.1 (by decide)
    have patUp : ∀ i, pat (rep (zi i) ∪ Kc i : Finset (Fin n)) = zi i := by
      intro i
      funext j
      by_cases h : j = i
      · rw [h, hz0]
        exact (pat0 _ i).2 (iff_of_true (Finset.mem_union.2 (Or.inr ((mK _ _).2 (colU i))))
          (Finset.mem_union.2 (Or.inr ((mK _ _).2 (colV i)))))
      · have o : ∀ w, color w = j → (bit w (rep (zi i) ∪ Kc i : Finset (Fin n)) = bit w (rep (zi i))) := by
          intro w hw
          rw [Bool.eq_iff_iff, bitT, bitT]
          exact ⟨fun k => (Finset.mem_union.1 k).resolve_right (fun l => h (hw.symm.trans ((mK _ _).1 l))),
            fun k => Finset.mem_union.2 (Or.inl k)⟩
        have e := congrFun (patRep (zi i)) j
        rw [← e]
        rw [patG (rep (zi i) ∪ Kc i : Finset (Fin n)) j _ _ rfl rfl, patG (rep (zi i)) j _ _ rfl rfl, o (U j) (colU j), o (V j) (colV j)]
    let A1 : Finset (Finset (Fin n)) := P.image rep
    let A2 : Finset (Finset (Fin n)) := Finset.univ.image (fun i => rep (zi i) ∪ Kc i)
    let A : Finset W := A1 ∪ A2
    have in1 : ∀ z ∈ P, (rep z : W) ∈ A := fun z hz => Finset.mem_union.2 (Or.inl (Finset.mem_image_of_mem _ hz))
    have in2 : ∀ i, (rep (zi i) ∪ Kc i : Finset (Fin n)) ∈ (A : Finset (Finset (Fin n))) := fun i =>
      Finset.mem_union.2 (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have img : A.image pat = P := by
      ext z
      constructor
      · intro h
        obtain ⟨x, hx, e⟩ := PEqualNP.Outside.L_meta_53212.memI'' h
        rcases Finset.mem_union.1 (show (x : Finset (Fin n)) ∈ A1 ∪ A2 from hx) with h1 | h1
        · obtain ⟨y, hy, ey⟩ := Finset.mem_image.1 h1
          have : pat x = y := by rw [show x = rep y from ey.symm]; exact patRep y
          rw [← e, this]; exact hy
        · obtain ⟨i, -, ey⟩ := Finset.mem_image.1 h1
          have : pat x = zi i := by rw [show x = (rep (zi i) ∪ Kc i : Finset (Fin n)) from ey.symm]; exact patUp i
          rw [← e, this]; exact hzi i
      · intro h
        exact PEqualNP.Outside.L_meta_53212.memI'.symm' (in1 z h) (patRep z)
    refine ⟨A, img, (equiv A).2 ⟨?_, fun i => ?_⟩, ?_⟩
    · rw [img]; exact ⟨finj, fne, fun i => ⟨zi i, hzi i, hz0 i⟩, fno⟩
    · refine ⟨rep (zi i), in1 _ (hzi i), (rep (zi i) ∪ Kc i : Finset (Fin n)), in2 i, ?_⟩
      have u : U i ∈ Kc i := (mK _ _).2 (colU i)
      have v : V i ∈ Kc i := (mK _ _).2 (colV i)
      refine ⟨fun h => Finset.disjoint_left.1 (dis i) h u, fun h => Finset.disjoint_left.1 (dis i) h v, ?_⟩
      show (rep (zi i) ∪ Kc i : Finset (Fin n)) = _
      ext w
      constructor
      · intro hw
        rcases Finset.mem_union.1 hw with h | h
        · exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr (PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr h)))
        · have cw := (mK i w).1 h
          rcases cases_ w with e | e
          · rw [cw] at e; exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inl e)
          · rw [cw] at e
            exact PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inr (PEqualNP.Outside.L_meta_53212.memIns.2 (Or.inl e)))
      · intro hw
        refine Finset.mem_union.2 ?_
        rcases PEqualNP.Outside.L_meta_53212.memIns.1 hw with h | h
        · exact Or.inr (h ▸ u)
        rcases PEqualNP.Outside.L_meta_53212.memIns.1 h with h | h
        · exact Or.inr (h ▸ v)
        · exact Or.inl h
    · have c1 : A1.card ≤ P.card := Finset.card_image_le
      have c2 : A2.card ≤ m := Finset.card_image_le.trans (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin]))
      have c3 : A.card ≤ A1.card + A2.card := PEqualNP.Outside.L_meta_53212.cardU
      omega
