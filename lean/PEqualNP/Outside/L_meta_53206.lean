import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53206

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

/-- Los pares validos definidos por desigualdades lineales tienen una base finita de pares indescomponibles. -/
lemma basis {X β : Type} [Fintype X] [DecidableEq X] [Finite β] (T : β → Finset X)
    (valid : ℕ → (X → ℕ) → Prop) (char : ∀ D w, valid D w ↔ ∀ b, D ≤ ∑ x ∈ T b, w x) :
    ∃ P : Finset (ℕ × (X → ℕ)),
      (∀ h, h ∈ P ↔ (valid h.1 h.2 ∧ (h.1 ≠ 0 ∨ h.2 ≠ 0) ∧
        ∀ (a b : ℕ) (u v : X → ℕ), valid a u → valid b v → a+b = h.1 → u+v = h.2 → (a=0 ∧ u=0) ∨ (b=0 ∧ v=0))) ∧
      ∀ (D : ℕ) (w : X → ℕ), valid D w ↔
        ∃ k : ℕ × (X → ℕ) → ℕ, D = ∑ h ∈ P, k h * h.1 ∧ ∀ x : X, w x = ∑ h ∈ P, k h * h.2 x := by
  classical
  have zero : valid 0 0 := (char _ _).2 (fun _ => Nat.zero_le _)
  have add : ∀ a u b v, valid a u → valid b v → valid (a+b) (u+v) := by
    intro a u b v hu hv
    rw [char] at hu hv ⊢
    intro c
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact Nat.add_le_add (hu c) (hv c)
  let prim : ℕ × (X → ℕ) → Prop := fun h => valid h.1 h.2 ∧ (h.1 ≠ 0 ∨ h.2 ≠ 0) ∧
    ∀ (a b : ℕ) (u v : X → ℕ), valid a u → valid b v → a+b = h.1 → u+v = h.2 → (a=0 ∧ u=0) ∨ (b=0 ∧ v=0)
  have finite : {h | prim h}.Finite := by
    by_contra inf
    let f := Set.Infinite.natEmbedding _ inf
    let φ : ℕ × (X → ℕ) → (Unit ⊕ X ⊕ β) → ℕ := fun h =>
      Sum.elim (fun _ => h.1) (Sum.elim h.2 (fun c => (∑ x ∈ T c, h.2 x) - h.1))
    have wqo : WellQuasiOrdered (α := (Unit ⊕ X ⊕ β) → ℕ) (· ≤ ·) := wellQuasiOrdered_le
    obtain ⟨m, n, lt, le⟩ := wqo (fun i => φ (f i).1)
    set q := (f m).1 with hq
    set p := (f n).1 with hp
    have pq : prim q := (f m).2
    have pp : prim p := (f n).2
    have h1 : q.1 ≤ p.1 := le (Sum.inl ())
    have h2 : q.2 ≤ p.2 := fun x => le (Sum.inr (Sum.inl x))
    have h3 : ∀ c, (∑ x ∈ T c, q.2 x) - q.1 ≤ (∑ x ∈ T c, p.2 x) - p.1 := fun c => le (Sum.inr (Sum.inr c))
    have diff : valid (p.1 - q.1) (p.2 - q.2) := by
      rw [char]
      intro c
      have vq := (char _ _).1 pq.1 c
      have vp := (char _ _).1 pp.1 c
      have s : (∑ x ∈ T c, (p.2 - q.2) x) + ∑ x ∈ T c, q.2 x = ∑ x ∈ T c, p.2 x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (h2 x))
      have := h3 c
      omega
    have e2 : q.2 + (p.2 - q.2) = p.2 := funext fun x => Nat.add_sub_cancel' (h2 x)
    rcases pp.2.2 q.1 (p.1 - q.1) q.2 (p.2 - q.2) pq.1 diff (Nat.add_sub_cancel' h1) e2 with ⟨z1, z2⟩ | ⟨z1, z2⟩
    · rcases pq.2.1 with h | h
      · exact h z1
      · exact h z2
    · have eq1 : p.1 = q.1 := by omega
      have eq2 : p.2 = q.2 := by rw [← e2, z2, add_zero]
      have : f n = f m := Subtype.ext (Prod.ext eq1 eq2)
      exact absurd (f.injective this) (Nat.ne_of_gt lt)
  refine ⟨finite.toFinset, fun h => finite.mem_toFinset, fun D w => ?_⟩
  set P := finite.toFinset with hP
  have mem : ∀ h, h ∈ P ↔ prim h := fun h => finite.mem_toFinset
  constructor
  · intro hv
    have all : ∀ N D (w : X → ℕ), D + ∑ x, w x = N → valid D w →
        ∃ k : ℕ × (X → ℕ) → ℕ, D = ∑ h ∈ P, k h * h.1 ∧ ∀ x : X, w x = ∑ h ∈ P, k h * h.2 x := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro D w hN hv
        by_cases z : D = 0 ∧ w = 0
        · refine ⟨fun _ => 0, ?_, fun x => ?_⟩
          · simp [z.1]
          · simp [z.2]
        by_cases pr : prim (D, w)
        · have inP : (D, w) ∈ P := (mem _).2 pr
          refine ⟨fun h => if h = (D, w) then 1 else 0, ?_, fun x => ?_⟩
          · simp only [ite_mul, one_mul, zero_mul]
            rw [Finset.sum_ite_eq', if_pos inP]
          · simp only [ite_mul, one_mul, zero_mul]
            rw [Finset.sum_ite_eq', if_pos inP]
        have nz : D ≠ 0 ∨ w ≠ 0 := by
          by_cases h : D = 0
          · exact Or.inr (fun e => z ⟨h, e⟩)
          · exact Or.inl h
        have split : ¬ ∀ (a b : ℕ) (u v : X → ℕ), valid a u → valid b v → a+b = D → u+v = w → (a=0 ∧ u=0) ∨ (b=0 ∧ v=0) :=
          fun h => pr ⟨hv, nz, h⟩
        simp only [not_forall] at split
        obtain ⟨a, b, u, v, hu, hv', ha, hu', no⟩ := split
        rw [not_or] at no
        have pos : ∀ (c : ℕ) (y : X → ℕ), ¬ (c = 0 ∧ y = 0) → 0 < c + ∑ x, y x := by
          intro c y h
          by_contra hh
          apply h
          have c0 : c = 0 := by omega
          have s0 : ∑ x, y x = 0 := by omega
          exact ⟨c0, funext fun x => Finset.sum_eq_zero_iff.1 s0 x (Finset.mem_univ x)⟩
        have total : (a + ∑ x, u x) + (b + ∑ x, v x) = N := by
          rw [← hN, ← ha, ← hu']
          simp only [Pi.add_apply, Finset.sum_add_distrib]
          omega
        have pa := pos a u no.1
        have pb := pos b v no.2
        obtain ⟨k1, e1, f1⟩ := ih (a + ∑ x, u x) (by omega) a u rfl hu
        obtain ⟨k2, e2, f2⟩ := ih (b + ∑ x, v x) (by omega) b v rfl hv'
        refine ⟨fun h => k1 h + k2 h, ?_, fun x => ?_⟩
        · rw [← ha, e1, e2, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun h _ => (Nat.add_mul _ _ _).symm)
        · rw [← hu', Pi.add_apply, f1, f2, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun h _ => (Nat.add_mul _ _ _).symm)
    exact all _ D w rfl hv
  · rintro ⟨k, hD, hw⟩
    have smul : ∀ (m : ℕ) (h : ℕ × (X → ℕ)), valid h.1 h.2 → valid (m * h.1) (fun x => m * h.2 x) := by
      intro m h hv
      rw [char] at hv ⊢
      intro c
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (hv c)
    have sum : ∀ Q : Finset (ℕ × (X → ℕ)), Q ⊆ P →
        valid (∑ h ∈ Q, k h * h.1) (fun x => ∑ h ∈ Q, k h * h.2 x) := by
      intro Q
      induction Q using Finset.induction with
      | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact zero
      | insert h Q hn ih =>
        intro sub
        have v1 := smul (k h) h ((mem h).1 (sub (Finset.mem_insert_self _ _))).1
        have v2 := ih ((Finset.subset_insert _ _).trans sub)
        have := add _ _ _ _ v1 v2
        simp only [Finset.sum_insert hn]
        exact this
    have := sum P (Finset.Subset.refl _)
    rw [← hD] at this
    have e : (fun x => ∑ h ∈ P, k h * h.2 x) = w := funext fun x => (hw x).symm
    rwa [e] at this

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

end PEqualNP.Outside.L_meta_53206

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53206 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
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
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let primitive := fun h : Nat × (W → Nat) =>
    valid h.1 h.2 ∧ (h.1 ≠ 0 ∨ h.2 ≠ 0) ∧
    ∀ (a b : Nat) (u v : W → Nat), valid a u → valid b v →
      a+b = h.1 → u+v = h.2 → (a=0 ∧ u=0) ∨ (b=0 ∧ v=0)
  ∃ P : Finset (Nat × (W → Nat)), (∀ h, h ∈ P ↔ primitive h) ∧
    ∀ (D : Nat) (w : W → Nat), valid D w ↔
      ∃ k : Nat × (W → Nat) → Nat,
        D = ∑ h ∈ P, k h * h.1 ∧
        ∀ x : W, w x = ∑ h ∈ P, k h * h.2 x := by
  intro n c E color hE hsurj hcomp W bit neg same raw need keeps valid primitive
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
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
    have ok0 : PEqualNP.Outside.L_meta_53206.Ok L.length [] := ⟨by simp, by simp⟩
    let Has := fun (g : List PEqualNP.CircuitLowerBounds.Gate) (f : W → Bool) => PEqualNP.Outside.L_meta_53206.Has L g f
    -- tres atomos de una arista con cuatro entradas disponibles
    have three : ∀ g, PEqualNP.Outside.L_meta_53206.Ok L.length g → ∀ e : Fin n × Fin n, ∀ a b c' d e' f' : W → Bool,
        Has g a → Has g b → Has g c' → Has g d → Has g e' → Has g f' →
        (∀ x, (a x && b x) = atom (e, 0) x) → (∀ x, (c' x && d x) = atom (e, 1) x) → (∀ x, (e' x && f' x) = atom (e, 2) x) →
        ∃ g', PEqualNP.Outside.L_meta_53206.Ext L.length g g' ∧ g'.length = g.length + 3 ∧ ∀ k, Has g' (atom (e, k)) := by
      intro g ok e a b c' d e' f' ha hb hc hd he hf q0 q1 q2
      obtain ⟨g1, x1, l1, h1⟩ := PEqualNP.Outside.L_meta_53206.Has.gate ok PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) ha hb
        (f := atom (e, 0)) (fun x => by rw [← q0]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g2, x2, l2, h2⟩ := PEqualNP.Outside.L_meta_53206.Has.gate x1.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
        (hc.mono x1) (hd.mono x1) (f := atom (e, 1)) (fun x => by rw [← q1]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval])
      obtain ⟨g3, x3, l3, h3⟩ := PEqualNP.Outside.L_meta_53206.Has.gate x2.1 PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
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
        (Tᶜ).card = m → S ⊆ T → F ⊆ E → (∀ e ∈ F, e.1 ∈ T ∧ e.2 ∈ T) → PEqualNP.Outside.L_meta_53206.Ok L.length g →
        (∀ v ∈ T, Has g (neg v)) → (∀ e ∈ F, ∀ k, Has g (atom (e, k))) → g.length + S.card = 3 * F.card + T.card →
        ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
          PEqualNP.Outside.L_meta_53206.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
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
        have bitHas : ∀ i, Has g (bit i) := fun i => PEqualNP.Outside.L_meta_53206.Has.input g (inRaw _ (rawB i))
        have sHas : Has g (same e) := PEqualNP.Outside.L_meta_53206.Has.input g (inRaw _ (rawS e he))
        have dHas : Has g (fun x => !(same e x)) := PEqualNP.Outside.L_meta_53206.Has.input g (inRaw _ (rawD e he))
        have step : ∀ v, v ∉ T → (v = e.1 ∨ v = e.2) → (∀ w, (w = e.1 ∨ w = e.2) → w ≠ v → w ∈ T) →
            ∀ g3 : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.Outside.L_meta_53206.Ext L.length g g3 → g3.length = g.length + 3 →
            (∀ k, Has g3 (atom (e, k))) → ∀ i j : Fin 3, (∀ x, (atom (e, i) x || atom (e, j) x) = neg v x) →
            ∃ (F' : Finset (Fin n × Fin n)) (g' : List PEqualNP.CircuitLowerBounds.Gate), F' ⊆ E ∧
              PEqualNP.Outside.L_meta_53206.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F', ∀ k, Has g' (atom (e, k))) ∧
              g'.length + S.card = 3 * F'.card + n := by
          intro v vT vend other g3 x3 l3 h3 i j hor
          obtain ⟨g4, x4, l4, h4⟩ := PEqualNP.Outside.L_meta_53206.Has.gate x3.1 PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl)
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
      (fun v hv => PEqualNP.Outside.L_meta_53206.Has.input [] (inL _ (Or.inr (Finset.mem_image_of_mem _ hv))))
      (by simp) (by simp)
    have rest : ∀ R : Finset (Fin n × Fin n), R ⊆ E → Disjoint F R →
        ∃ g', PEqualNP.Outside.L_meta_53206.Ok L.length g' ∧ (∀ v, Has g' (neg v)) ∧ (∀ e ∈ F ∪ R, ∀ k, Has g' (atom (e, k))) ∧
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
        have bitHas : ∀ i, Has g1 (bit i) := fun i => PEqualNP.Outside.L_meta_53206.Has.input g1 (inRaw _ (rawB i))
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
    refine ⟨⟨g', 0⟩, ?_, PEqualNP.Outside.L_meta_53206.reads_of_ok' ok' 0, ?_, ?_, ?_⟩
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
  have up : ∀ A B : Finset W, A ⊆ B → keeps A → keeps B := by
    intro A B sub h S p
    constructor
    · rintro ⟨C, c1, c2, c3, c4, c5⟩
      refine (h S p).1 ⟨C, c1, c2, c3, c4, fun f hf => ?_⟩
      obtain ⟨j, hj, w⟩ := c5 f hf
      exact ⟨j, hj, fun x hx => w x (sub hx)⟩
    · exact build B S p
  have char : ∀ (D : ℕ) (w : W → ℕ), valid D w ↔
      ∀ b : {B : Finset W // ¬ keeps B}, D ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∉ b.1), w x := by
    intro D w
    constructor
    · intro hv b
      by_contra hlt
      let lost : W → ℕ := fun x => if x ∉ b.1 then w x else 0
      have total : (∑ x, lost x) < D := by
        have : (∑ x, lost x) = ∑ x ∈ Finset.univ.filter (fun x => x ∉ b.1), w x := by
          rw [Finset.sum_filter]
        omega
      refine b.2 (up _ b.1 (fun x hx => ?_) (hv lost total))
      have h := (PEqualNP.Outside.L_meta_53206.memF.1 hx).2
      by_contra hb
      simp only [lost, if_pos hb] at h
      exact lt_irrefl _ h
    · intro hall lost total
      by_contra hk
      have h1 := hall ⟨_, hk⟩
      have h2 : ∑ x ∈ Finset.univ.filter (fun x => x ∉ Finset.univ.filter (fun x => lost x < w x)), w x ≤ ∑ x, lost x := by
        refine le_trans (Finset.sum_le_sum (fun x hx => ?_))
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
        have h := (PEqualNP.Outside.L_meta_53206.memF.1 hx).2
        by_contra hc
        exact h (PEqualNP.Outside.L_meta_53206.memF.2 ⟨Finset.mem_univ _, not_le.1 hc⟩)
      dsimp only at h1
      refine absurd (le_trans h1 (le_trans (le_of_eq ?_) h2)) (not_le.2 total)
      exact Finset.sum_congr (Finset.ext fun x => by
        simp only [PEqualNP.Outside.L_meta_53206.memF]) (fun _ _ => rfl)
  have key := PEqualNP.Outside.L_meta_53206.basis (X := W) (β := {B : Finset W // ¬ keeps B})
    (fun b => Finset.univ.filter (fun x => x ∉ b.1)) valid char
  convert key
