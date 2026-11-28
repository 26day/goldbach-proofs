import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1466_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive SForm (k : Nat) where
  | const (b : Bool)
  | lit (j : Fin k) (pol : Bool)
  | and (l r : SForm k)
  | or (l r : SForm k)

def SForm.eval {k : Nat} (Y : Finset (Fin k)) : SForm k → Bool
  | .const b => b
  | .lit j pol => if pol then decide (j ∈ Y) else !decide (j ∈ Y)
  | .and l r => l.eval Y && r.eval Y
  | .or l r => l.eval Y || r.eval Y

def SForm.neg {k : Nat} : SForm k → SForm k
  | .const b => .const (!b)
  | .lit j pol => .lit j (!pol)
  | .and l r => .or l.neg r.neg
  | .or l r => .and l.neg r.neg

def SForm.posCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = true ∧ j ∈ J then 1 else 0
  | .and l r => l.posCount J + r.posCount J
  | .or l r => l.posCount J + r.posCount J

def SForm.negCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = false ∧ j ∈ J then 1 else 0
  | .and l r => l.negCount J + r.negCount J
  | .or l r => l.negCount J + r.negCount J

def SForm.posVars {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit j pol => if pol then {j} else ∅
  | .and l r => l.posVars ∪ r.posVars
  | .or l r => l.posVars ∪ r.posVars

def SForm.negVars {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit j pol => if pol then ∅ else {j}
  | .and l r => l.negVars ∪ r.negVars
  | .or l r => l.negVars ∪ r.negVars

def SForm.andConf {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit _ _ => ∅
  | .and l r => l.andConf ∪ r.andConf ∪ ((l.posVars ∩ r.negVars) ∪ (l.negVars ∩ r.posVars))
  | .or l r => l.andConf ∪ r.andConf

def SForm.orConf {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit _ _ => ∅
  | .and l r => l.orConf ∪ r.orConf
  | .or l r => l.orConf ∪ r.orConf ∪ ((l.posVars ∩ r.negVars) ∪ (l.negVars ∩ r.posVars))

def SForm.markTuple {k : Nat} (F : SForm k) :
    (Finset (Fin k) × Finset (Fin k)) × (Finset (Fin k) × Finset (Fin k)) :=
  ((F.posVars, F.negVars), (F.andConf, F.orConf))

lemma SForm.eval_neg {k : Nat} (Y : Finset (Fin k)) (F : SForm k) :
    F.neg.eval Y = !(F.eval Y) := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.eval]
  | and l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]

lemma SForm.posCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.posCount J = F.negCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

lemma SForm.negCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.negCount J = F.posCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

lemma SForm.posVars_neg {k : Nat} (F : SForm k) : F.neg.posVars = F.negVars := by
  induction F with
  | const _ => rfl
  | lit j pol => cases pol <;> rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]

lemma SForm.negVars_neg {k : Nat} (F : SForm k) : F.neg.negVars = F.posVars := by
  induction F with
  | const _ => rfl
  | lit j pol => cases pol <;> rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]

lemma SForm.andConf_neg {k : Nat} (F : SForm k) : F.neg.andConf = F.orConf := by
  induction F with
  | const _ => rfl
  | lit _ _ => rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr]
  | or l r ihl ihr =>
    simp only [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr, SForm.posVars_neg, SForm.negVars_neg]
    ext x; simp; tauto

lemma SForm.orConf_neg {k : Nat} (F : SForm k) : F.neg.orConf = F.andConf := by
  induction F with
  | const _ => rfl
  | lit _ _ => rfl
  | and l r ihl ihr =>
    simp only [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr, SForm.posVars_neg, SForm.negVars_neg]
    ext x; simp; tauto
  | or l r ihl ihr => simp [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr]

lemma SForm.andConf_sub_posVars {k : Nat} (F : SForm k) : F.andConf ⊆ F.posVars := by
  induction F with
  | const _ => exact Finset.Subset.rfl
  | lit _ _ => exact Finset.empty_subset _
  | and l r ihl ihr =>
    intro x hx
    simp only [SForm.andConf, SForm.posVars, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with (h | h) | (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
    · exact Or.inl h
    · exact Or.inr h
  | or l r ihl ihr =>
    intro x hx
    simp only [SForm.andConf, SForm.posVars, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

lemma SForm.orConf_sub_posVars {k : Nat} (F : SForm k) : F.orConf ⊆ F.posVars := by
  induction F with
  | const _ => exact Finset.Subset.rfl
  | lit _ _ => exact Finset.empty_subset _
  | and l r ihl ihr =>
    intro x hx
    simp only [SForm.orConf, SForm.posVars, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
  | or l r ihl ihr =>
    intro x hx
    simp only [SForm.orConf, SForm.posVars, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with (h | h) | (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
    · exact Or.inl h
    · exact Or.inr h

lemma SForm.posCount_add_disjoint {k : Nat} {A B : Finset (Fin k)} (hAB : Disjoint A B) (F : SForm k) :
    F.posCount (A ∪ B) = F.posCount A + F.posCount B := by
  induction F with
  | const _ => rfl
  | lit j pol =>
    cases pol with
    | false => simp [SForm.posCount]
    | true =>
      by_cases hA : j ∈ A
      · have hB : j ∉ B := Finset.disjoint_left.mp hAB hA
        simp [SForm.posCount, hA, hB]
      · by_cases hB : j ∈ B <;> simp [SForm.posCount, hA, hB]
  | and l r ihl ihr => simp only [SForm.posCount, ihl, ihr]; omega
  | or l r ihl ihr => simp only [SForm.posCount, ihl, ihr]; omega

lemma SForm.posCount_ge_card_inter_posVars {k : Nat} (K : Finset (Fin k)) (F : SForm k) :
    (K ∩ F.posVars).card ≤ F.posCount K := by
  induction F with
  | const _ => simp [SForm.posVars, SForm.posCount]
  | lit j pol =>
    cases pol with
    | false => simp [SForm.posVars, SForm.posCount]
    | true =>
      by_cases hj : j ∈ K
      · have heq : K ∩ {j} = {j} := by ext x; simp [hj]
        simp [SForm.posVars, SForm.posCount, heq, hj]
      · have heq : K ∩ {j} = ∅ := by ext x; simp; intro h1 h2; subst h2; exact hj h1
        simp [SForm.posVars, SForm.posCount, heq, hj]
  | and l r ihl ihr =>
    simp only [SForm.posVars, SForm.posCount, Finset.inter_union_distrib_left]
    calc (K ∩ l.posVars ∪ K ∩ r.posVars).card
        ≤ (K ∩ l.posVars).card + (K ∩ r.posVars).card := Finset.card_union_le _ _
      _ ≤ l.posCount K + r.posCount K := Nat.add_le_add ihl ihr
  | or l r ihl ihr =>
    simp only [SForm.posVars, SForm.posCount, Finset.inter_union_distrib_left]
    calc (K ∩ l.posVars ∪ K ∩ r.posVars).card
        ≤ (K ∩ l.posVars).card + (K ∩ r.posVars).card := Finset.card_union_le _ _
      _ ≤ l.posCount K + r.posCount K := Nat.add_le_add ihl ihr

def stepForm {k : Nat} (fs : List (SForm k)) (g : Gate) : SForm k :=
  match g.op, g.inputs with
  | .not, [] => .const true
  | .not, a :: _ => (fs.getD a (.const false)).neg
  | .and, [] => .const true
  | .and, [a] => fs.getD a (.const false)
  | .and, a :: b :: _ => .and (fs.getD a (.const false)) (fs.getD b (.const false))
  | .or, [] => .const false
  | .or, [a] => fs.getD a (.const false)
  | .or, a :: b :: _ => .or (fs.getD a (.const false)) (fs.getD b (.const false))
  | _, _ => .const false

lemma getD_append_singleton {α : Type*} (l : List α) (x d : α) (i : Nat) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have hnone : ([x] : List α)[i - l.length]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [hnone]; rfl

lemma mark_singleton_and {α : Type*} [DecidableEq α] (a b c d : Finset α) :
    ((a, b), (c, d)) = ((a ∪ ∅, b ∪ ∅), ((c ∪ ∅) ∪ ((a ∩ ∅) ∪ (b ∩ ∅)), d ∪ ∅)) := by
  simp

lemma mark_singleton_or {α : Type*} [DecidableEq α] (a b c d : Finset α) :
    ((a, b), (c, d)) = ((a ∪ ∅, b ∪ ∅), (c ∪ ∅, (d ∪ ∅) ∪ ((a ∩ ∅) ∪ (b ∩ ∅)))) := by
  simp

lemma unfold_circuit {k : Nat} (D : Circuit) (hfit : FanInTwo D) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    ∃ F : SForm k,
      (∀ Y : Finset (Fin k),
        F.eval Y = (D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true])).getD D.output false) ∧
      (∀ J : Finset (Fin k),
        (F.posCount J, F.negCount J) =
          ((D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
            let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
              let z := zs.getD j (0, 0)
              (acc.1 + z.1, acc.2 + z.2)) (0, 0)
            let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
            zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab])
            (List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)])).getD D.output (0, 0))) ∧
      F.markTuple =
        (let V := Finset (Fin k)
         let Z : (V × V) × (V × V) := ((∅, ∅), (∅, ∅))
         let xs := List.ofFn (fun j : Fin k => ((({j}, ∅), (∅, ∅)) : (V × V) × (V × V))) ++ [Z, Z]
         let ws := D.gates.foldl (fun (ts : List ((V × V) × (V × V))) g =>
           let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
           let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
           let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
           let u := a.2.1 ∪ b.2.1
           let v := a.2.2 ∪ b.2.2
           ts ++ [if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
             else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
               if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))]) xs
         ws.getD D.output Z) := by
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let V := Finset (Fin k)
  let Z : (V × V) × (V × V) := ((∅, ∅), (∅, ∅))
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let stepC : List (Nat × Nat) → Gate → List (Nat × Nat) := fun zs g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0, 0)
      (acc.1 + z.1, acc.2 + z.2)) (0, 0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
    zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab]
  let stepM : List ((V × V) × (V × V)) → Gate → List ((V × V) × (V × V)) := fun ts g =>
    let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
    let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
    let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
    let u := a.2.1 ∪ b.2.1
    let v := a.2.2 ∪ b.2.2
    ts ++ [if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
      else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
        if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))]
  let stepF : List (SForm k) → Gate → List (SForm k) := fun fs g =>
    fs ++ [stepForm fs g]
  have hgen : ∀ (gs : List Gate) (fs : List (SForm k))
      (zs : Finset (Fin k) → List (Nat × Nat))
      (ws : Finset (Fin k) → List Bool)
      (ts : List ((V × V) × (V × V))),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ J, fs.length = (zs J).length) →
      (∀ Y, fs.length = (ws Y).length) →
      fs.length = ts.length →
      (∀ Y i, (fs.getD i (.const false)).eval Y = (ws Y).getD i false) →
      (∀ J i, (fs.getD i (.const false)).posCount J = ((zs J).getD i (0, 0)).1 ∧
              (fs.getD i (.const false)).negCount J = ((zs J).getD i (0, 0)).2) →
      (∀ i, (fs.getD i (.const false)).markTuple = ts.getD i Z) →
      let fs' := gs.foldl stepF fs
      let ts' := gs.foldl stepM ts
      (∀ Y i, (fs'.getD i (.const false)).eval Y = (gs.foldl stepW (ws Y)).getD i false) ∧
      (∀ J i, (fs'.getD i (.const false)).posCount J = ((gs.foldl stepC (zs J)).getD i (0, 0)).1 ∧
              (fs'.getD i (.const false)).negCount J = ((gs.foldl stepC (zs J)).getD i (0, 0)).2) ∧
      (∀ i, (fs'.getD i (.const false)).markTuple = ts'.getD i Z) := by
    intro gs
    induction gs with
    | nil =>
      intro fs zs ws ts _ _ _ _ hev hcnt hmk
      exact ⟨hev, hcnt, hmk⟩
    | cons g rest ih =>
      intro fs zs ws ts hgs hlenZ hlenW hlenT hev hcnt hmk
      simp only [List.foldl_cons]
      have hg := hgs g (by simp)
      have hrest : ∀ g' ∈ rest, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      have hstep_ev : ∀ Y, (stepForm fs g).eval Y = g.op.eval (g.inputs.map fun i => (ws Y).getD i false) := by
        intro Y
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hev Y a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, GateOp.eval, SForm.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hev Y a, hev Y b]
            | cons d e =>
              have hlen := hg.2
              rw [hin] at hlen
              simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hev Y a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, GateOp.eval, SForm.eval, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hev Y a, hev Y b]
            | cons d e =>
              have hlen := hg.2
              rw [hin] at hlen
              simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, SForm.eval_neg, List.map_cons, List.headD_cons]
            rw [hev Y a]
      have hstep_cnt : ∀ J,
          (stepForm fs g).posCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => (zs J).getD j (0, 0))).getD (0, 0)).2
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := (zs J).getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).1) ∧
          (stepForm fs g).negCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => (zs J).getD j (0, 0))).getD (0, 0)).1
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := (zs J).getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).2) := by
        intro J
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
              Nat.zero_add]
            exact hcnt J a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
                Nat.zero_add, SForm.posCount, SForm.negCount]
              exact ⟨by rw [(hcnt J a).1, (hcnt J b).1], by rw [(hcnt J a).2, (hcnt J b).2]⟩
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
              Nat.zero_add]
            exact hcnt J a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
                Nat.zero_add, SForm.posCount, SForm.negCount]
              exact ⟨by rw [(hcnt J a).1, (hcnt J b).1], by rw [(hcnt J a).2, (hcnt J b).2]⟩
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, ↓reduceIte, SForm.posCount_neg, SForm.negCount_neg,
              List.head?_cons, Option.map_some, Option.getD_some]
            exact ⟨(hcnt J a).2, (hcnt J a).1⟩
      have hstep_mk : (stepForm fs g).markTuple =
          (let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
           let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
           let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
           let u := a.2.1 ∪ b.2.1
           let v := a.2.2 ∪ b.2.2
           if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
           else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
             if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))) := by
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, eq_self, reduceCtorEq, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_nil,
              Option.map_none, Option.getD_none]
            rw [← hmk a]
            exact mark_singleton_and _ _ _ _
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
                Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
              rw [← hmk a, ← hmk b]
              simp only [SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
              convert rfl
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_nil,
              Option.map_none, Option.getD_none]
            rw [← hmk a]
            exact mark_singleton_or _ _ _ _
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
                Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
              rw [← hmk a, ← hmk b]
              simp only [SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
              convert rfl
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some]
            rw [← hmk a]
            simp [SForm.markTuple, SForm.posVars_neg, SForm.negVars_neg,
              SForm.andConf_neg, SForm.orConf_neg]
      apply ih (stepF fs g) (fun J => stepC (zs J) g) (fun Y => stepW (ws Y) g) (stepM ts g) hrest
      · intro J; simp [stepF, stepC, hlenZ J]
      · intro Y; simp [stepF, stepW, hlenW Y]
      · simp [stepF, stepM, hlenT]
      · intro Y i
        simp only [stepF, stepW, getD_append_singleton, hlenW Y]
        by_cases h1 : i < (ws Y).length
        · rw [if_pos h1, if_pos h1]; exact hev Y i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = (ws Y).length
          · rw [if_pos h2, if_pos h2]; exact hstep_ev Y
          · rw [if_neg h2, if_neg h2]; rfl
      · intro J i
        simp only [stepF, stepC, getD_append_singleton, hlenZ J]
        by_cases h1 : i < (zs J).length
        · rw [if_pos h1, if_pos h1]; exact hcnt J i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = (zs J).length
          · rw [if_pos h2, if_pos h2]
            by_cases hnot : g.op = GateOp.not
            · rw [if_pos hnot]
              have hc := hstep_cnt J
              rw [if_pos hnot, if_pos hnot] at hc
              exact hc
            · rw [if_neg hnot]
              have hc := hstep_cnt J
              rw [if_neg hnot, if_neg hnot] at hc
              exact hc
          · rw [if_neg h2, if_neg h2]; exact ⟨rfl, rfl⟩
      · intro i
        simp only [stepF, stepM, getD_append_singleton, hlenT]
        by_cases h1 : i < ts.length
        · rw [if_pos h1, if_pos h1]; exact hmk i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = ts.length
          · rw [if_pos h2, if_pos h2]; exact hstep_mk
          · rw [if_neg h2, if_neg h2]; rfl
  let fs0 : List (SForm k) := List.ofFn (fun j : Fin k => SForm.lit j true) ++ [.const false, .const true]
  let zs0 : Finset (Fin k) → List (Nat × Nat) := fun J =>
    List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)]
  let ws0 : Finset (Fin k) → List Bool := fun Y =>
    List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true]
  let ts0 : List ((V × V) × (V × V)) :=
    List.ofFn (fun j : Fin k => ((({j}, ∅), (∅, ∅)) : (V × V) × (V × V))) ++ [Z, Z]
  have hgs : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hfit g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  have hbase := hgen D.gates fs0 zs0 ws0 ts0 hgs
    (fun J => by simp [fs0, zs0])
    (fun Y => by simp [fs0, ws0])
    (by simp [fs0, ts0])
    (fun Y i => by
      simp only [fs0, ws0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]; simp [h1, SForm.eval]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · rfl
        · rfl
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([false, true] : List Bool)[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; rfl)
    (fun J i => by
      simp only [fs0, zs0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]; simp [h1, SForm.posCount, SForm.negCount]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([(0, 0), (0, 0)] : List (Nat × Nat))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; exact ⟨rfl, rfl⟩)
    (fun i => by
      simp only [fs0, ts0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]
        simp [h1, SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · rfl
        · rfl
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([Z, Z] : List ((V × V) × (V × V)))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; rfl)
  refine ⟨(D.gates.foldl stepF fs0).getD D.output (.const false), ?_, ?_, ?_⟩
  · intro Y; exact hbase.1 Y D.output
  · intro J; exact Prod.ext (hbase.2.1 J D.output).1 (hbase.2.1 J D.output).2
  · exact hbase.2.2 D.output

lemma SForm.eval_mono_vars {k : Nat} (F : SForm k) {Y1 Y2 : Finset (Fin k)}
    (hpos : ∀ j ∈ F.posVars, j ∈ Y1 → j ∈ Y2)
    (hneg : ∀ j ∈ F.negVars, j ∈ Y2 → j ∈ Y1) :
    F.eval Y1 = true → F.eval Y2 = true := by
  induction F with
  | const b => exact id
  | lit j pol =>
    cases pol with
    | true =>
      simp only [SForm.eval, ↓reduceIte, decide_eq_true_eq]
      exact hpos j (by simp [SForm.posVars])
    | false =>
      simp only [SForm.eval, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
        decide_eq_false_iff_not]
      intro h1 h2
      exact h1 (hneg j (by simp [SForm.negVars]) h2)
  | and l r ihl ihr =>
    simp only [SForm.eval, Bool.and_eq_true]
    intro ⟨hl, hr⟩
    refine ⟨ihl (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                (fun j hj => hneg j (by simp [SForm.negVars, hj])) hl,
            ihr (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                (fun j hj => hneg j (by simp [SForm.negVars, hj])) hr⟩
  | or l r ihl ihr =>
    simp only [SForm.eval, Bool.or_eq_true]
    intro h
    rcases h with hl | hr
    · exact Or.inl (ihl (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                        (fun j hj => hneg j (by simp [SForm.negVars, hj])) hl)
    · exact Or.inr (ihr (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                        (fun j hj => hneg j (by simp [SForm.negVars, hj])) hr)

def SForm.repNeg {k : Nat} (J : Finset (Fin k)) (c : Bool) : SForm k → SForm k
  | .const b => .const b
  | .lit j pol => if pol = false ∧ j ∈ J then .const c else .lit j pol
  | .and l r => .and (l.repNeg J c) (r.repNeg J c)
  | .or l r => .or (l.repNeg J c) (r.repNeg J c)

lemma SForm.posCount_repNeg {k : Nat} (J : Finset (Fin k)) (c : Bool) (F : SForm k) :
    (F.repNeg J c).posCount J = F.posCount J := by
  induction F with
  | const _ => rfl
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg, SForm.posCount]
    | false =>
      simp only [SForm.repNeg, true_and, SForm.posCount, Bool.false_eq_true, false_and, ↓reduceIte]
      split_ifs <;> simp [SForm.posCount]
  | and l r ihl ihr => simp [SForm.repNeg, SForm.posCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.repNeg, SForm.posCount, ihl, ihr]

lemma SForm.negVars_repNeg_disjoint {k : Nat} (J : Finset (Fin k)) (c : Bool) (F : SForm k) :
    Disjoint (F.repNeg J c).negVars J := by
  induction F with
  | const _ => simp [SForm.repNeg, SForm.negVars]
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg, SForm.negVars]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, SForm.negVars, hj]
      · simp [SForm.repNeg, SForm.negVars, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.negVars]
    exact Finset.disjoint_union_left.mpr ⟨ihl, ihr⟩
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.negVars]
    exact Finset.disjoint_union_left.mpr ⟨ihl, ihr⟩

lemma SForm.eval_imp_repTrue {k : Nat} (J : Finset (Fin k)) (F : SForm k) (Y : Finset (Fin k)) :
    F.eval Y = true → (F.repNeg J true).eval Y = true := by
  induction F with
  | const _ => exact id
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, hj, SForm.eval]
      · simp [SForm.repNeg, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨ihl h1, ihr h2⟩
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_true]
    exact fun h => h.elim (fun h1 => Or.inl (ihl h1)) (fun h2 => Or.inr (ihr h2))

lemma SForm.eval_false_imp_repFalse {k : Nat} (J : Finset (Fin k)) (F : SForm k) (Y : Finset (Fin k)) :
    F.eval Y = false → (F.repNeg J false).eval Y = false := by
  induction F with
  | const _ => exact id
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, hj, SForm.eval]
      · simp [SForm.repNeg, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_false_iff]
    exact fun h => h.elim (fun h1 => Or.inl (ihl h1)) (fun h2 => Or.inr (ihr h2))
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_false_iff]
    exact fun ⟨h1, h2⟩ => ⟨ihl h1, ihr h2⟩

lemma SForm.repTrue_exists_sub {k : Nat} (J U : Finset (Fin k)) (hUJ : Disjoint U J) (F : SForm k)
    (hconf : Disjoint J F.andConf) :
    ∀ S ⊆ J, (F.repNeg J true).eval (U ∪ S) = true → ∃ S' ⊆ S, F.eval (U ∪ S') = true := by
  induction F with
  | const b =>
    intro S _ h; exact ⟨S, Finset.Subset.rfl, h⟩
  | lit j pol =>
    intro S _ h
    cases pol with
    | true => exact ⟨S, Finset.Subset.rfl, by simpa [SForm.repNeg] using h⟩
    | false =>
      by_cases hj : j ∈ J
      · refine ⟨∅, Finset.empty_subset _, ?_⟩
        have hjU : j ∉ U := Finset.disjoint_right.mp hUJ hj
        simp [SForm.eval, hjU]
      · exact ⟨S, Finset.Subset.rfl, by simpa [SForm.repNeg, hj] using h⟩
  | and l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_true] at h
    have hcl : Disjoint J l.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    have hcr : Disjoint J r.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    obtain ⟨S1, hS1S, h1⟩ := ihl hcl S hSJ h.1
    obtain ⟨S2, hS2S, h2⟩ := ihr hcr S hSJ h.2
    let S' := (S1 ∩ l.posVars) ∪ (S2 ∩ r.posVars)
    refine ⟨S', Finset.union_subset
      (Finset.Subset.trans Finset.inter_subset_left hS1S)
      (Finset.Subset.trans Finset.inter_subset_left hS2S), ?_⟩
    simp only [SForm.eval, Bool.and_eq_true]
    refine ⟨SForm.eval_mono_vars l ?_ ?_ h1, SForm.eval_mono_vars r ?_ ?_ h2⟩
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS1
      · exact Or.inl hU
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hS1, hj⟩))
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS'
      · exact Or.inl hU
      · rcases Finset.mem_union.mp hS' with hA | hB
        · exact Or.inr (Finset.mem_inter.mp hA).1
        · exfalso
          have hB' := Finset.mem_inter.mp hB
          have hjJ : j ∈ J := hSJ (hS2S hB'.1)
          have hjC : j ∈ (SForm.and l r).andConf := by
            simp [SForm.andConf, hj, hB'.2]
          exact Finset.disjoint_left.mp hconf hjJ hjC
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS2
      · exact Or.inl hU
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS2, hj⟩))
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS'
      · exact Or.inl hU
      · rcases Finset.mem_union.mp hS' with hA | hB
        · exfalso
          have hA' := Finset.mem_inter.mp hA
          have hjJ : j ∈ J := hSJ (hS1S hA'.1)
          have hjC : j ∈ (SForm.and l r).andConf := by
            simp [SForm.andConf, hj, hA'.2]
          exact Finset.disjoint_left.mp hconf hjJ hjC
        · exact Or.inr (Finset.mem_inter.mp hB).1
  | or l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_true] at h
    have hcl : Disjoint J l.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    have hcr : Disjoint J r.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    rcases h with hl | hr
    · obtain ⟨S1, hS1S, h1⟩ := ihl hcl S hSJ hl
      exact ⟨S1, hS1S, by simp [SForm.eval, h1]⟩
    · obtain ⟨S2, hS2S, h2⟩ := ihr hcr S hSJ hr
      exact ⟨S2, hS2S, by simp [SForm.eval, h2]⟩

lemma SForm.repFalse_exists_sup {k : Nat} (J U : Finset (Fin k)) (F : SForm k)
    (hconf : Disjoint J F.orConf) :
    ∀ S ⊆ J, (F.repNeg J false).eval (U ∪ S) = false → ∃ S', S ⊆ S' ∧ S' ⊆ J ∧ F.eval (U ∪ S') = false := by
  induction F with
  | const b =>
    intro S hSJ h; exact ⟨S, Finset.Subset.rfl, hSJ, h⟩
  | lit j pol =>
    intro S hSJ h
    cases pol with
    | true => exact ⟨S, Finset.Subset.rfl, hSJ, by simpa [SForm.repNeg] using h⟩
    | false =>
      by_cases hj : j ∈ J
      · refine ⟨J, hSJ, Finset.Subset.rfl, ?_⟩
        simp [SForm.eval, hj]
      · exact ⟨S, Finset.Subset.rfl, hSJ, by simpa [SForm.repNeg, hj] using h⟩
  | and l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_false_iff] at h
    have hcl : Disjoint J l.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    have hcr : Disjoint J r.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    rcases h with hl | hr
    · obtain ⟨S1, hSS1, hS1J, h1⟩ := ihl hcl S hSJ hl
      exact ⟨S1, hSS1, hS1J, by simp [SForm.eval, h1]⟩
    · obtain ⟨S2, hSS2, hS2J, h2⟩ := ihr hcr S hSJ hr
      exact ⟨S2, hSS2, hS2J, by simp [SForm.eval, h2]⟩
  | or l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_false_iff] at h
    have hcl : Disjoint J l.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    have hcr : Disjoint J r.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    obtain ⟨S1, hSS1, hS1J, h1⟩ := ihl hcl S hSJ h.1
    obtain ⟨S2, hSS2, hS2J, h2⟩ := ihr hcr S hSJ h.2
    let S' := S ∪ (S1 ∩ l.negVars) ∪ (S2 ∩ r.negVars)
    have hSS' : S ⊆ S' := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
    have hS'J : S' ⊆ J := Finset.union_subset
      (Finset.union_subset hSJ (Finset.Subset.trans Finset.inter_subset_left hS1J))
      (Finset.Subset.trans Finset.inter_subset_left hS2J)
    refine ⟨S', hSS', hS'J, ?_⟩
    simp only [SForm.eval, Bool.or_eq_false_iff]
    constructor
    · cases hlv : l.eval (U ∪ S') with
      | false => rfl
      | true =>
        exfalso
        have hlt : l.eval (U ∪ S1) = true := SForm.eval_mono_vars l ?_ ?_ hlv
        · rw [h1] at hlt; exact absurd hlt (by decide)
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS'
          · exact Or.inl hU
          · rcases Finset.mem_union.mp hS' with hA | hB
            · rcases Finset.mem_union.mp hA with hS | h1n
              · exact Or.inr (hSS1 hS)
              · exact Or.inr (Finset.mem_inter.mp h1n).1
            · exfalso
              have hB' := Finset.mem_inter.mp hB
              have hjJ : j ∈ J := hS2J hB'.1
              have hjC : j ∈ (SForm.or l r).orConf := by
                simp [SForm.orConf, hj, hB'.2]
              exact Finset.disjoint_left.mp hconf hjJ hjC
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS1
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS1, hj⟩)))
    · cases hrv : r.eval (U ∪ S') with
      | false => rfl
      | true =>
        exfalso
        have hrt : r.eval (U ∪ S2) = true := SForm.eval_mono_vars r ?_ ?_ hrv
        · rw [h2] at hrt; exact absurd hrt (by decide)
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS'
          · exact Or.inl hU
          · rcases Finset.mem_union.mp hS' with hA | hB
            · rcases Finset.mem_union.mp hA with hS | h1n
              · exact Or.inr (hSS2 hS)
              · exfalso
                have h1n' := Finset.mem_inter.mp h1n
                have hjJ : j ∈ J := hS1J h1n'.1
                have hjC : j ∈ (SForm.or l r).orConf := by
                  simp [SForm.orConf, hj, h1n'.2]
                exact Finset.disjoint_left.mp hconf hjJ hjC
            · exact Or.inr (Finset.mem_inter.mp hB).1
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS2
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS2, hj⟩))

lemma mono_eval_sub {k : Nat} (J U : Finset (Fin k)) (M : SForm k) (hmono : Disjoint M.negVars J)
    {S1 S2 : Finset (Fin k)} (hS12 : S1 ⊆ S2) (hS2J : S2 ⊆ J) :
    M.eval (U ∪ S1) = true → M.eval (U ∪ S2) = true := by
  apply SForm.eval_mono_vars M
  · intro j _ hmem
    exact Finset.union_subset_union_right hS12 hmem
  · intro j hj hmem
    simp only [Finset.mem_union] at hmem ⊢
    rcases hmem with hU | hS2
    · exact Or.inl hU
    · exact absurd (hS2J hS2) (Finset.disjoint_left.mp hmono hj)

lemma mono_pq_bound {k : Nat} (J U : Finset (Fin k)) (hUJ : Disjoint U J) (M : SForm k) :
    Disjoint M.negVars J →
    ∀ p q : Nat,
      (∀ S ⊆ J, S.card < p → M.eval (U ∪ S) = false) →
      (∀ R ⊆ J, R.card < q → M.eval (U ∪ (J \ R)) = true) →
      p * q ≤ M.posCount J := by
  classical
  induction M with
  | const b =>
    intro _ p q hp hq
    cases b with
    | false =>
      cases q with
      | zero => simp
      | succ q' =>
        have h := hq ∅ (Finset.empty_subset _) (by simp)
        simp [SForm.eval] at h
    | true =>
      cases p with
      | zero => simp
      | succ p' =>
        have h := hp ∅ (Finset.empty_subset _) (by simp)
        simp [SForm.eval] at h
  | lit j pol =>
    intro hmono p q hp hq
    by_cases hjJ : j ∈ J
    · cases pol with
      | false =>
        exfalso
        exact Finset.disjoint_left.mp hmono (by simp [SForm.negVars]) hjJ
      | true =>
        have hp1 : p ≤ 1 := by
          by_contra hgt
          have h := hp {j} (Finset.singleton_subset_iff.mpr hjJ) (by simp; omega)
          simp [SForm.eval] at h
        have hq1 : q ≤ 1 := by
          by_contra hgt
          have hjU : j ∉ U := Finset.disjoint_right.mp hUJ hjJ
          have h := hq {j} (Finset.singleton_subset_iff.mpr hjJ) (by simp; omega)
          simp [SForm.eval, hjU] at h
        simp only [SForm.posCount, hjJ, and_self, ↓reduceIte]
        nlinarith
    · have heq : ∀ S ⊆ J, (SForm.lit j pol).eval (U ∪ S) = (SForm.lit j pol).eval U := by
        intro S hSJ
        have hjS : j ∉ S := fun h => hjJ (hSJ h)
        cases pol <;> simp [SForm.eval, hjS]
      cases hv : (SForm.lit j pol).eval U with
      | false =>
        cases q with
        | zero => simp
        | succ q' =>
          have h := hq ∅ (Finset.empty_subset _) (by simp)
          rw [heq (J \ ∅) Finset.sdiff_subset, hv] at h
          exact absurd h (by decide)
      | true =>
        cases p with
        | zero => simp
        | succ p' =>
          have h := hp ∅ (Finset.empty_subset _) (by simp)
          rw [heq ∅ (Finset.empty_subset _), hv] at h
          exact absurd h (by decide)
  | and l r ihl ihr =>
    intro hmono p q hp hq
    have hml : Disjoint l.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hmr : Disjoint r.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hql : ∀ R ⊆ J, R.card < q → l.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      have h := hq R hRJ hRc
      simp [SForm.eval] at h; exact h.1
    have hqr : ∀ R ⊆ J, R.card < q → r.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      have h := hq R hRJ hRc
      simp [SForm.eval] at h; exact h.2
    let Ll := (J.powerset.filter (fun S => l.eval (U ∪ S) = true)).image Finset.card
    let Lr := (J.powerset.filter (fun S => r.eval (U ∪ S) = true)).image Finset.card
    by_cases hle : Ll.Nonempty
    · by_cases hre : Lr.Nonempty
      · let p1 := Ll.min' hle
        let p2 := Lr.min' hre
        have hp1m : p1 ∈ Ll := Finset.min'_mem Ll hle
        have hp2m : p2 ∈ Lr := Finset.min'_mem Lr hre
        obtain ⟨S1, hS1f, hS1c⟩ := Finset.mem_image.mp hp1m
        obtain ⟨S2, hS2f, hS2c⟩ := Finset.mem_image.mp hp2m
        have hS1p := Finset.mem_filter.mp hS1f
        have hS2p := Finset.mem_filter.mp hS2f
        have hS1J : S1 ⊆ J := Finset.mem_powerset.mp hS1p.1
        have hS2J : S2 ⊆ J := Finset.mem_powerset.mp hS2p.1
        have hp_le : p ≤ p1 + p2 := by
          by_contra hgt
          have hcard : (S1 ∪ S2).card < p := by
            have := Finset.card_union_le S1 S2
            omega
          have hfalse := hp (S1 ∪ S2) (Finset.union_subset hS1J hS2J) hcard
          have h1t : l.eval (U ∪ (S1 ∪ S2)) = true :=
            mono_eval_sub J U l hml Finset.subset_union_left (Finset.union_subset hS1J hS2J) hS1p.2
          have h2t : r.eval (U ∪ (S1 ∪ S2)) = true :=
            mono_eval_sub J U r hmr Finset.subset_union_right (Finset.union_subset hS1J hS2J) hS2p.2
          simp [SForm.eval, h1t, h2t] at hfalse
        have hpl : ∀ S ⊆ J, S.card < p1 → l.eval (U ∪ S) = false := by
          intro S hSJ hSc
          cases hv : l.eval (U ∪ S) with
          | false => rfl
          | true =>
            exfalso
            have hmem : S.card ∈ Ll :=
              Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSJ, hv⟩, rfl⟩
            have hmin := Finset.min'_le Ll S.card hmem
            omega
        have hpr : ∀ S ⊆ J, S.card < p2 → r.eval (U ∪ S) = false := by
          intro S hSJ hSc
          cases hv : r.eval (U ∪ S) with
          | false => rfl
          | true =>
            exfalso
            have hmem : S.card ∈ Lr :=
              Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSJ, hv⟩, rfl⟩
            have hmin := Finset.min'_le Lr S.card hmem
            omega
        have hb1 := ihl hml p1 q hpl hql
        have hb2 := ihr hmr p2 q hpr hqr
        simp only [SForm.posCount]
        calc p * q ≤ (p1 + p2) * q := Nat.mul_le_mul_right q hp_le
          _ = p1 * q + p2 * q := Nat.add_mul p1 p2 q
          _ ≤ l.posCount J + r.posCount J := Nat.add_le_add hb1 hb2
      · cases q with
        | zero => simp
        | succ q' =>
          exfalso
          have ht := hqr ∅ (Finset.empty_subset _) (by simp)
          have hmem : (J \ ∅).card ∈ Lr :=
            Finset.mem_image.mpr ⟨J \ ∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ht⟩, rfl⟩
          exact hre ⟨_, hmem⟩
    · cases q with
      | zero => simp
      | succ q' =>
        exfalso
        have ht := hql ∅ (Finset.empty_subset _) (by simp)
        have hmem : (J \ ∅).card ∈ Ll :=
          Finset.mem_image.mpr ⟨J \ ∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ht⟩, rfl⟩
        exact hle ⟨_, hmem⟩
  | or l r ihl ihr =>
    intro hmono p q hp hq
    have hml : Disjoint l.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hmr : Disjoint r.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hpl : ∀ S ⊆ J, S.card < p → l.eval (U ∪ S) = false := by
      intro S hSJ hSc
      have h := hp S hSJ hSc
      simp [SForm.eval] at h; exact h.1
    have hpr : ∀ S ⊆ J, S.card < p → r.eval (U ∪ S) = false := by
      intro S hSJ hSc
      have h := hp S hSJ hSc
      simp [SForm.eval] at h; exact h.2
    let Rl := (J.powerset.filter (fun R => l.eval (U ∪ (J \ R)) = false)).image Finset.card
    let Rr := (J.powerset.filter (fun R => r.eval (U ∪ (J \ R)) = false)).image Finset.card
    by_cases hle : Rl.Nonempty
    · by_cases hre : Rr.Nonempty
      · let q1 := Rl.min' hle
        let q2 := Rr.min' hre
        have hq1m : q1 ∈ Rl := Finset.min'_mem Rl hle
        have hq2m : q2 ∈ Rr := Finset.min'_mem Rr hre
        obtain ⟨R1, hR1f, hR1c⟩ := Finset.mem_image.mp hq1m
        obtain ⟨R2, hR2f, hR2c⟩ := Finset.mem_image.mp hq2m
        have hR1p := Finset.mem_filter.mp hR1f
        have hR2p := Finset.mem_filter.mp hR2f
        have hR1J : R1 ⊆ J := Finset.mem_powerset.mp hR1p.1
        have hR2J : R2 ⊆ J := Finset.mem_powerset.mp hR2p.1
        have hq_le : q ≤ q1 + q2 := by
          by_contra hgt
          have hcard : (R1 ∪ R2).card < q := by
            have := Finset.card_union_le R1 R2
            omega
          have htrue := hq (R1 ∪ R2) (Finset.union_subset hR1J hR2J) hcard
          simp only [SForm.eval, Bool.or_eq_true] at htrue
          rcases htrue with h1t | h2t
          · have h1' := mono_eval_sub J U l hml
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left)
              Finset.sdiff_subset h1t
            rw [hR1p.2] at h1'; exact absurd h1' (by decide)
          · have h2' := mono_eval_sub J U r hmr
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_right)
              Finset.sdiff_subset h2t
            rw [hR2p.2] at h2'; exact absurd h2' (by decide)
        have hql : ∀ R ⊆ J, R.card < q1 → l.eval (U ∪ (J \ R)) = true := by
          intro R hRJ hRc
          cases hv : l.eval (U ∪ (J \ R)) with
          | true => rfl
          | false =>
            exfalso
            have hmem : R.card ∈ Rl :=
              Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hRJ, hv⟩, rfl⟩
            have hmin := Finset.min'_le Rl R.card hmem
            omega
        have hqr : ∀ R ⊆ J, R.card < q2 → r.eval (U ∪ (J \ R)) = true := by
          intro R hRJ hRc
          cases hv : r.eval (U ∪ (J \ R)) with
          | true => rfl
          | false =>
            exfalso
            have hmem : R.card ∈ Rr :=
              Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hRJ, hv⟩, rfl⟩
            have hmin := Finset.min'_le Rr R.card hmem
            omega
        have hb1 := ihl hml p q1 hpl hql
        have hb2 := ihr hmr p q2 hpr hqr
        simp only [SForm.posCount]
        calc p * q ≤ p * (q1 + q2) := Nat.mul_le_mul_left p hq_le
          _ = p * q1 + p * q2 := Nat.mul_add p q1 q2
          _ ≤ l.posCount J + r.posCount J := Nat.add_le_add hb1 hb2
      · cases p with
        | zero => simp
        | succ p' =>
          exfalso
          have hf := hpr ∅ (Finset.empty_subset _) (by simp)
          have heq : J \ J = ∅ := Finset.sdiff_self J
          have hmem : J.card ∈ Rr :=
            Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, by rwa [heq]⟩, rfl⟩
          exact hre ⟨_, hmem⟩
    · cases p with
      | zero => simp
      | succ p' =>
        exfalso
        have hf := hpl ∅ (Finset.empty_subset _) (by simp)
        have heq : J \ J = ∅ := Finset.sdiff_self J
        have hmem : J.card ∈ Rl :=
          Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, by rwa [heq]⟩, rfl⟩
        exact hle ⟨_, hmem⟩


lemma SForm.negCount_ge_card_inter_negVars {k : Nat} (K : Finset (Fin k)) (F : SForm k) :
    (K ∩ F.negVars).card ≤ F.negCount K := by
  have h := SForm.posCount_ge_card_inter_posVars K F.neg
  rwa [SForm.posVars_neg, SForm.posCount_neg] at h

lemma SForm.andConf_sub_negVars {k : Nat} (F : SForm k) : F.andConf ⊆ F.negVars := by
  have h := SForm.orConf_sub_posVars F.neg
  rwa [SForm.orConf_neg, SForm.posVars_neg] at h

lemma SForm.orConf_sub_negVars {k : Nat} (F : SForm k) : F.orConf ⊆ F.negVars := by
  have h := SForm.andConf_sub_posVars F.neg
  rwa [SForm.andConf_neg, SForm.posVars_neg] at h

lemma SForm.negCount_add_disjoint {k : Nat} {A B : Finset (Fin k)} (hAB : Disjoint A B) (F : SForm k) :
    F.negCount (A ∪ B) = F.negCount A + F.negCount B := by
  have h := SForm.posCount_add_disjoint hAB F.neg
  rwa [SForm.posCount_neg, SForm.posCount_neg, SForm.posCount_neg] at h

lemma SForm.posCount_eq_zero_of_disjoint {k : Nat} (K : Finset (Fin k)) (F : SForm k)
    (h : Disjoint K F.posVars) : F.posCount K = 0 := by
  induction F with
  | const _ => rfl
  | lit j pol =>
    cases pol with
    | false => simp [SForm.posCount]
    | true =>
      have : j ∉ K := by
        intro hj
        exact Finset.disjoint_left.mp h hj (by simp [SForm.posVars])
      simp [SForm.posCount, this]
  | and l r ihl ihr =>
    simp only [SForm.posVars, Finset.disjoint_union_right] at h
    simp [SForm.posCount, ihl h.1, ihr h.2]
  | or l r ihl ihr =>
    simp only [SForm.posVars, Finset.disjoint_union_right] at h
    simp [SForm.posCount, ihl h.1, ihr h.2]

lemma SForm.posCount_single_pos {k : Nat} (F : SForm k) (j : Fin k) :
    0 < F.posCount {j} ↔ j ∈ F.posVars := by
  constructor
  · intro h
    by_contra hj
    have := SForm.posCount_eq_zero_of_disjoint {j} F (by simpa using hj)
    omega
  · intro hj
    have h := SForm.posCount_ge_card_inter_posVars {j} F
    have : ({j} : Finset (Fin k)) ∩ F.posVars = {j} := by ext x; simp; intro hx; subst hx; exact hj
    rw [this, Finset.card_singleton] at h
    omega

lemma SForm.negCount_single_pos {k : Nat} (F : SForm k) (j : Fin k) :
    0 < F.negCount {j} ↔ j ∈ F.negVars := by
  have h := SForm.posCount_single_pos F.neg j
  rwa [SForm.posCount_neg, SForm.posVars_neg] at h

lemma SForm.posCount_split {k : Nat} (F : SForm k) {J : Finset (Fin k)} {j : Fin k} (hj : j ∈ J) :
    F.posCount J = F.posCount {j} + F.posCount (J \ {j}) := by
  have h := SForm.posCount_add_disjoint (A := {j}) (B := J \ {j}) Finset.disjoint_sdiff F
  rw [← h, Finset.union_sdiff_of_subset (by simpa using hj)]

lemma SForm.negCount_split {k : Nat} (F : SForm k) {J : Finset (Fin k)} {j : Fin k} (hj : j ∈ J) :
    F.negCount J = F.negCount {j} + F.negCount (J \ {j}) := by
  have h := SForm.negCount_add_disjoint (A := {j}) (B := J \ {j}) Finset.disjoint_sdiff F
  rw [← h, Finset.union_sdiff_of_subset (by simpa using hj)]

lemma SForm.posCount_sum {k : Nat} (F : SForm k) (J : Finset (Fin k)) :
    F.posCount J = ∑ j ∈ J, F.posCount {j} := by
  induction J using Finset.induction_on with
  | empty => simp [SForm.posCount_eq_zero_of_disjoint]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq]
    exact SForm.posCount_add_disjoint (by simpa using ha) F

lemma SForm.posCount_mono {k : Nat} (F : SForm k) {J K : Finset (Fin k)} (h : J ⊆ K) :
    F.posCount J ≤ F.posCount K := by
  have e := SForm.posCount_add_disjoint (A := J) (B := K \ J) Finset.disjoint_sdiff F
  rw [Finset.union_sdiff_of_subset h] at e
  omega

lemma SForm.negCount_mono {k : Nat} (F : SForm k) {J K : Finset (Fin k)} (h : J ⊆ K) :
    F.negCount J ≤ F.negCount K := by
  have e := SForm.negCount_add_disjoint (A := J) (B := K \ J) Finset.disjoint_sdiff F
  rw [Finset.union_sdiff_of_subset h] at e
  omega

lemma SForm.eval_congr_vars {k : Nat} (F : SForm k) {Y1 Y2 : Finset (Fin k)}
    (h : ∀ j, j ∈ F.posVars ∨ j ∈ F.negVars → (j ∈ Y1 ↔ j ∈ Y2)) :
    F.eval Y1 = F.eval Y2 := by
  have h12 := SForm.eval_mono_vars F (Y1 := Y1) (Y2 := Y2)
    (fun j hj hm => (h j (Or.inl hj)).mp hm) (fun j hj hm => (h j (Or.inr hj)).mpr hm)
  have h21 := SForm.eval_mono_vars F (Y1 := Y2) (Y2 := Y1)
    (fun j hj hm => (h j (Or.inl hj)).mpr hm) (fun j hj hm => (h j (Or.inr hj)).mp hm)
  cases h1 : F.eval Y1 <;> cases h2 : F.eval Y2
  · rfl
  · rw [h21 h2] at h1; exact absurd h1 (by decide)
  · rw [h12 h1] at h2; exact absurd h2 (by decide)
  · rfl

lemma SForm.conf_unique {k : Nat} (m : Fin k) (F : SForm k) :
    F.posCount {m} ≤ 1 → F.negCount {m} ≤ 1 → m ∈ F.andConf → m ∉ F.orConf := by
  induction F with
  | const _ => intro _ _ h; simp [SForm.andConf] at h
  | lit _ _ => intro _ _ h; simp [SForm.andConf] at h
  | and l r ihl ihr =>
    intro hp hn ha ho
    simp only [SForm.posCount] at hp
    simp only [SForm.negCount] at hn
    simp only [SForm.andConf, SForm.orConf, Finset.mem_union, Finset.mem_inter] at ha ho
    have lp := SForm.posCount_single_pos l m
    have ln := SForm.negCount_single_pos l m
    have rp := SForm.posCount_single_pos r m
    have rn := SForm.negCount_single_pos r m
    have lap := SForm.andConf_sub_posVars l
    have lan := SForm.andConf_sub_negVars l
    have rap := SForm.andConf_sub_posVars r
    have ran := SForm.andConf_sub_negVars r
    have lop := SForm.orConf_sub_posVars l
    have lon := SForm.orConf_sub_negVars l
    have rop := SForm.orConf_sub_posVars r
    have ron := SForm.orConf_sub_negVars r
    rcases ha with (h | h) | (h | h)
    · rcases ho with h' | h'
      · exact ihl (by omega) (by omega) h h'
      · have a1 := lp.mpr (lap h); have a2 := rp.mpr (rop h'); omega
    · rcases ho with h' | h'
      · have a1 := rp.mpr (rap h); have a2 := lp.mpr (lop h'); omega
      · exact ihr (by omega) (by omega) h h'
    · rcases ho with h' | h'
      · have a1 := rn.mpr h.2; have a2 := ln.mpr (lon h'); omega
      · have a1 := lp.mpr h.1; have a2 := rp.mpr (rop h'); omega
    · rcases ho with h' | h'
      · have a1 := rp.mpr h.2; have a2 := lp.mpr (lop h'); omega
      · have a1 := ln.mpr h.1; have a2 := rn.mpr (ron h'); omega
  | or l r ihl ihr =>
    intro hp hn ha ho
    simp only [SForm.posCount] at hp
    simp only [SForm.negCount] at hn
    simp only [SForm.andConf, SForm.orConf, Finset.mem_union, Finset.mem_inter] at ha ho
    have lp := SForm.posCount_single_pos l m
    have ln := SForm.negCount_single_pos l m
    have rp := SForm.posCount_single_pos r m
    have rn := SForm.negCount_single_pos r m
    have lap := SForm.andConf_sub_posVars l
    have lan := SForm.andConf_sub_negVars l
    have rap := SForm.andConf_sub_posVars r
    have ran := SForm.andConf_sub_negVars r
    have lop := SForm.orConf_sub_posVars l
    have rop := SForm.orConf_sub_posVars r
    rcases ha with h | h
    · have a1 := lp.mpr (lap h); have a2 := ln.mpr (lan h)
      rcases ho with (h' | h') | (h' | h')
      · exact ihl (by omega) (by omega) h h'
      · have a3 := rp.mpr (rop h'); omega
      · have a3 := rn.mpr h'.2; omega
      · have a3 := rp.mpr h'.2; omega
    · have a1 := rp.mpr (rap h); have a2 := rn.mpr (ran h)
      rcases ho with (h' | h') | (h' | h')
      · have a3 := lp.mpr (lop h'); omega
      · exact ihr (by omega) (by omega) h h'
      · have a3 := lp.mpr h'.1; omega
      · have a3 := ln.mpr h'.1; omega

lemma pin_bound {k : Nat} (F : SForm k) (A B H : Finset (Fin k)) (p q : Nat) (hAB : A ⊆ B)
    (hH_eq : H = B \ A)
    (hprot : ∀ Y, A ⊆ Y → Y ⊆ B → (((Y \ A).card < p → F.eval Y = false) ∧ ((B \ Y).card < q → F.eval Y = true)))
    (T : Finset (Fin k)) (hT_eq : T = F.andConf ∨ T = F.orConf)
    (K : Finset (Fin k)) (z : Nat)
    (hHTK : H ∩ T ⊆ K) (hKH : K ⊆ H) (hzK : z ≤ K.card) (hzp : z < p) (hKzq : K.card - z < q) :
    (p - z) * (q - (K.card - z)) ≤ F.posCount (H \ K) := by
  obtain ⟨Z, hZK, hZc⟩ := Finset.exists_subset_card_eq hzK
  let J := H \ K
  let U := A ∪ Z
  have hHA : Disjoint A H := by rw [hH_eq]; exact Finset.disjoint_sdiff
  have hAJ : Disjoint A J := Finset.disjoint_of_subset_right Finset.sdiff_subset hHA
  have hZJ : Disjoint Z J := Finset.disjoint_of_subset_left hZK Finset.sdiff_disjoint.symm
  have hUJ : Disjoint U J := Finset.disjoint_union_left.mpr ⟨hAJ, hZJ⟩
  have hAZ : Disjoint A Z := Finset.disjoint_of_subset_right (Finset.Subset.trans hZK hKH) hHA
  have hJT : Disjoint J T := by
    rw [Finset.disjoint_left]
    intro j hjJ hjT
    have hjH : j ∈ H := (Finset.mem_sdiff.mp hjJ).1
    have hjK : j ∉ K := (Finset.mem_sdiff.mp hjJ).2
    exact hjK (hHTK (by convert Finset.mem_inter.mpr ⟨hjH, hjT⟩))
  have hY_sub : ∀ S ⊆ J, A ⊆ U ∪ S ∧ U ∪ S ⊆ B := by
    intro S hSJ
    refine ⟨Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left,
            Finset.union_subset (Finset.union_subset hAB ?_) ?_⟩
    · have : Z ⊆ B \ A := by rw [← hH_eq]; exact Finset.Subset.trans hZK hKH
      exact Finset.Subset.trans this Finset.sdiff_subset
    · have : S ⊆ B \ A := by rw [← hH_eq]; exact Finset.Subset.trans hSJ Finset.sdiff_subset
      exact Finset.Subset.trans this Finset.sdiff_subset
  have hF_false : ∀ S ⊆ J, S.card < p - z → F.eval (U ∪ S) = false := by
    intro S hSJ hSc
    have hsub := hY_sub S hSJ
    have hAS : Disjoint A S := Finset.disjoint_of_subset_right hSJ hAJ
    have hZS : Disjoint Z S := Finset.disjoint_of_subset_right hSJ hZJ
    have hcard : ((U ∪ S) \ A).card < p := by
      have heq : (U ∪ S) \ A = Z ∪ S := by
        calc (U ∪ S) \ A = (A ∪ (Z ∪ S)) \ A := by rw [Finset.union_assoc]
          _ = Z ∪ S := Finset.union_sdiff_cancel_left (Finset.disjoint_union_right.mpr ⟨hAZ, hAS⟩)
      rw [heq, Finset.card_union_of_disjoint hZS, hZc]
      omega
    exact (hprot (U ∪ S) hsub.1 hsub.2).1 (by convert hcard)
  have hF_true : ∀ R ⊆ J, R.card < q - (K.card - z) → F.eval (U ∪ (J \ R)) = true := by
    intro R hRJ hRc
    have hsub := hY_sub (J \ R) Finset.sdiff_subset
    have hcard : (B \ (U ∪ (J \ R))).card < q := by
      have hdisj1 : Disjoint (K \ Z) R :=
        Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right hRJ Finset.sdiff_disjoint.symm)
      have heq : B \ (U ∪ (J \ R)) = (K \ Z) ∪ R := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union, U, J]
        constructor
        · intro ⟨hxB, hxnot⟩
          push_neg at hxnot
          have hxH : x ∈ H := by rw [hH_eq]; exact Finset.mem_sdiff.mpr ⟨hxB, hxnot.1.1⟩
          by_cases hxK : x ∈ K
          · exact Or.inl ⟨hxK, hxnot.1.2⟩
          · by_cases hxR : x ∈ R
            · exact Or.inr hxR
            · exfalso; tauto
        · intro hx
          rcases hx with ⟨hxK, hxZ⟩ | hxR
          · have hxH : x ∈ H := hKH hxK
            rw [hH_eq] at hxH
            have hxBA := Finset.mem_sdiff.mp hxH
            refine ⟨hxBA.1, ?_⟩
            intro hm
            rcases hm with (hA | hZ) | hJR
            · exact hxBA.2 hA
            · exact hxZ hZ
            · exact hJR.1.2 hxK
          · have hxJ : x ∈ H \ K := hRJ hxR
            have hxH : x ∈ H := (Finset.mem_sdiff.mp hxJ).1
            have hxK : x ∉ K := (Finset.mem_sdiff.mp hxJ).2
            rw [hH_eq] at hxH
            have hxBA := Finset.mem_sdiff.mp hxH
            refine ⟨hxBA.1, ?_⟩
            intro hm
            rcases hm with (hA | hZ) | hJR
            · exact hxBA.2 hA
            · exact hxK (hZK hZ)
            · exact hJR.2 hxR
      rw [heq, Finset.card_union_of_disjoint hdisj1,
          Finset.card_sdiff, Finset.inter_eq_left.mpr hZK, hZc]
      omega
    exact (hprot (U ∪ (J \ R)) hsub.1 hsub.2).2 (by convert hcard)
  rcases hT_eq with rfl | rfl
  · let M := F.repNeg J true
    have hMp : ∀ S ⊆ J, S.card < p - z → M.eval (U ∪ S) = false := by
      intro S hSJ hSc
      cases hv : M.eval (U ∪ S) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨S', hS'S, hS't⟩ := SForm.repTrue_exists_sub J U hUJ F hJT S hSJ hv
        have hS'f := hF_false S' (Finset.Subset.trans hS'S hSJ) (lt_of_le_of_lt (Finset.card_le_card hS'S) hSc)
        rw [hS'f] at hS't; exact absurd hS't (by decide)
    have hMq : ∀ R ⊆ J, R.card < q - (K.card - z) → M.eval (U ∪ (J \ R)) = true := fun R hRJ hRc =>
      SForm.eval_imp_repTrue J F _ (hF_true R hRJ hRc)
    have hb := mono_pq_bound J U hUJ M
      (SForm.negVars_repNeg_disjoint J true F)
      (p - z) (q - (K.card - z)) hMp hMq
    rwa [SForm.posCount_repNeg] at hb
  · let M := F.repNeg J false
    have hMp : ∀ S ⊆ J, S.card < p - z → M.eval (U ∪ S) = false := fun S hSJ hSc =>
      SForm.eval_false_imp_repFalse J F _ (hF_false S hSJ hSc)
    have hMq : ∀ R ⊆ J, R.card < q - (K.card - z) → M.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      cases hv : M.eval (U ∪ (J \ R)) with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨S', hSS', hS'J, hS'f⟩ :=
          SForm.repFalse_exists_sup J U F hJT (J \ R) Finset.sdiff_subset hv
        let R' := J \ S'
        have hR'R : R' ⊆ R := by
          intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          by_contra hxR
          exact hx'.2 (hSS' (Finset.mem_sdiff.mpr ⟨hx'.1, hxR⟩))
        have hJR' : J \ R' = S' := Finset.sdiff_sdiff_eq_self hS'J
        have hR't := hF_true R' Finset.sdiff_subset (lt_of_le_of_lt (Finset.card_le_card hR'R) hRc)
        rw [hJR', hS'f] at hR't; exact absurd hR't (by decide)
    have hb := mono_pq_bound J U hUJ M
      (SForm.negVars_repNeg_disjoint J false F)
      (p - z) (q - (K.card - z)) hMp hMq
    rwa [SForm.posCount_repNeg] at hb

lemma tight_zero {k : Nat} (J : Finset (Fin k)) (M : SForm k) (h : M.posCount J = 0) :
    (∀ j ∈ J, M.posCount {j} ≤ 1) ∧ (∀ j ∈ J, j ∉ M.posVars) := by
  constructor
  · intro j hj
    have := SForm.posCount_mono M (Finset.singleton_subset_iff.mpr hj)
    omega
  · intro j hj hjv
    have h1 := (SForm.posCount_single_pos M j).mpr hjv
    have := SForm.posCount_mono M (Finset.singleton_subset_iff.mpr hj)
    omega

lemma mono_tight {k : Nat} (J U : Finset (Fin k)) (hUJ : Disjoint U J) (M : SForm k) :
    Disjoint M.negVars J →
    ∀ p q : Nat,
      (∀ S ⊆ J, S.card < p → M.eval (U ∪ S) = false) →
      (∀ R ⊆ J, R.card < q → M.eval (U ∪ (J \ R)) = true) →
      M.posCount J ≤ p * q →
      (∀ j ∈ J, M.posCount {j} ≤ 1) ∧
      (∀ j ∈ J, j ∈ M.posVars →
        (∃ S ⊆ J, j ∈ S ∧ S.card ≤ p ∧ M.eval (U ∪ S) = true) ∧
        (∃ R ⊆ J, j ∈ R ∧ R.card ≤ q ∧ M.eval (U ∪ (J \ R)) = false)) := by
  classical
  induction M with
  | const b =>
    intro _ p q _ _ _
    have h0 := tight_zero J (SForm.const b) rfl
    exact ⟨h0.1, fun j hj hjv => absurd hjv (h0.2 j hj)⟩
  | lit j pol =>
    intro hmono p q hp hq hP
    by_cases hjJ : j ∈ J
    · cases pol with
      | false =>
        exfalso
        exact Finset.disjoint_left.mp hmono (by simp [SForm.negVars]) hjJ
      | true =>
        have hjU : j ∉ U := Finset.disjoint_right.mp hUJ hjJ
        have hp1 : p ≤ 1 := by
          by_contra hgt
          have h := hp {j} (Finset.singleton_subset_iff.mpr hjJ) (by simp; omega)
          simp [SForm.eval] at h
        have hq1 : q ≤ 1 := by
          by_contra hgt
          have h := hq {j} (Finset.singleton_subset_iff.mpr hjJ) (by simp; omega)
          simp [SForm.eval, hjU] at h
        simp only [SForm.posCount, hjJ, and_self, ↓reduceIte] at hP
        have hp1' : p = 1 := by
          rcases Nat.lt_or_ge p 1 with h | h
          · have : p = 0 := by omega
            subst this; simp at hP
          · omega
        have hq1' : q = 1 := by
          rcases Nat.lt_or_ge q 1 with h | h
          · have : q = 0 := by omega
            subst this; simp at hP
          · omega
        subst hp1' hq1'
        refine ⟨?_, ?_⟩
        · intro i _
          simp only [SForm.posCount]
          split_ifs <;> omega
        · intro i hi hiv
          have hij : i = j := by simpa [SForm.posVars] using hiv
          subst hij
          refine ⟨⟨{i}, Finset.singleton_subset_iff.mpr hi, by simp, by simp, by simp [SForm.eval]⟩,
            ⟨{i}, Finset.singleton_subset_iff.mpr hi, by simp, by simp, by simp [SForm.eval, hjU]⟩⟩
    · have h0 : (SForm.lit j pol).posCount J = 0 := by simp [SForm.posCount, hjJ]
      have h1 := tight_zero J (SForm.lit j pol) h0
      exact ⟨h1.1, fun i hi hiv => absurd hiv (h1.2 i hi)⟩
  | and l r ihl ihr =>
    intro hmono p q hp hq hP
    have hml : Disjoint l.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hmr : Disjoint r.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    by_cases hz : p = 0 ∨ q = 0
    · have h0 : (SForm.and l r).posCount J = 0 := by
        rcases hz with h | h <;> simp [h] at hP <;> exact hP
      have h1 := tight_zero J (SForm.and l r) h0
      exact ⟨h1.1, fun i hi hiv => absurd hiv (h1.2 i hi)⟩
    push_neg at hz
    obtain ⟨hp0, hq0⟩ := hz
    have hql : ∀ R ⊆ J, R.card < q → l.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      have h := hq R hRJ hRc
      simp [SForm.eval] at h; exact h.1
    have hqr : ∀ R ⊆ J, R.card < q → r.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      have h := hq R hRJ hRc
      simp [SForm.eval] at h; exact h.2
    let Ll := (J.powerset.filter (fun S => l.eval (U ∪ S) = true)).image Finset.card
    let Lr := (J.powerset.filter (fun S => r.eval (U ∪ S) = true)).image Finset.card
    have hle : Ll.Nonempty := by
      have ht := hql ∅ (Finset.empty_subset _) (by simp; omega)
      exact ⟨_, Finset.mem_image.mpr ⟨J \ ∅, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ht⟩, rfl⟩⟩
    have hre : Lr.Nonempty := by
      have ht := hqr ∅ (Finset.empty_subset _) (by simp; omega)
      exact ⟨_, Finset.mem_image.mpr ⟨J \ ∅, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ht⟩, rfl⟩⟩
    let p1 := Ll.min' hle
    let p2 := Lr.min' hre
    have hp1m : p1 ∈ Ll := Finset.min'_mem Ll hle
    have hp2m : p2 ∈ Lr := Finset.min'_mem Lr hre
    obtain ⟨S1, hS1f, hS1c⟩ := Finset.mem_image.mp hp1m
    obtain ⟨S2, hS2f, hS2c⟩ := Finset.mem_image.mp hp2m
    have hS1p := Finset.mem_filter.mp hS1f
    have hS2p := Finset.mem_filter.mp hS2f
    have hS1J : S1 ⊆ J := Finset.mem_powerset.mp hS1p.1
    have hS2J : S2 ⊆ J := Finset.mem_powerset.mp hS2p.1
    have hpl : ∀ S ⊆ J, S.card < p1 → l.eval (U ∪ S) = false := by
      intro S hSJ hSc
      cases hv : l.eval (U ∪ S) with
      | false => rfl
      | true =>
        exfalso
        have hmem : S.card ∈ Ll :=
          Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSJ, hv⟩, rfl⟩
        have hmin := Finset.min'_le Ll S.card hmem
        omega
    have hpr : ∀ S ⊆ J, S.card < p2 → r.eval (U ∪ S) = false := by
      intro S hSJ hSc
      cases hv : r.eval (U ∪ S) with
      | false => rfl
      | true =>
        exfalso
        have hmem : S.card ∈ Lr :=
          Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSJ, hv⟩, rfl⟩
        have hmin := Finset.min'_le Lr S.card hmem
        omega
    have hb1 := mono_pq_bound J U hUJ l hml p1 q hpl hql
    have hb2 := mono_pq_bound J U hUJ r hmr p2 q hpr hqr
    simp only [SForm.posCount] at hP
    have hsum : (p1 + p2) * q ≤ p * q := by rw [Nat.add_mul]; omega
    have hp12 : p1 + p2 ≤ p := Nat.le_of_mul_le_mul_right hsum (by omega)
    have hp_le : p ≤ p1 + p2 := by
      by_contra hgt
      have hcard : (S1 ∪ S2).card < p := by
        have := Finset.card_union_le S1 S2
        omega
      have hfalse := hp (S1 ∪ S2) (Finset.union_subset hS1J hS2J) hcard
      have h1t : l.eval (U ∪ (S1 ∪ S2)) = true :=
        mono_eval_sub J U l hml Finset.subset_union_left (Finset.union_subset hS1J hS2J) hS1p.2
      have h2t : r.eval (U ∪ (S1 ∪ S2)) = true :=
        mono_eval_sub J U r hmr Finset.subset_union_right (Finset.union_subset hS1J hS2J) hS2p.2
      simp [SForm.eval, h1t, h2t] at hfalse
    have hpeq : p = p1 + p2 := by omega
    have e1 : l.posCount J ≤ p1 * q := by
      have : p * q = p1 * q + p2 * q := by rw [hpeq, Nat.add_mul]
      omega
    have e2 : r.posCount J ≤ p2 * q := by
      have : p * q = p1 * q + p2 * q := by rw [hpeq, Nat.add_mul]
      omega
    obtain ⟨hl1, hl2⟩ := ihl hml p1 q hpl hql e1
    obtain ⟨hr1, hr2⟩ := ihr hmr p2 q hpr hqr e2
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [SForm.posCount]
      by_contra hgt
      have a1 := hl1 j hj
      have a2 := hr1 j hj
      have hjl : j ∈ l.posVars := (SForm.posCount_single_pos l j).mp (by omega)
      have hjr : j ∈ r.posVars := (SForm.posCount_single_pos r j).mp (by omega)
      obtain ⟨T1, hT1J, hjT1, hT1c, hT1e⟩ := (hl2 j hj hjl).1
      obtain ⟨T2, hT2J, hjT2, hT2c, hT2e⟩ := (hr2 j hj hjr).1
      have hinter : 0 < (T1 ∩ T2).card := Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨hjT1, hjT2⟩⟩
      have hcu := Finset.card_union_add_card_inter T1 T2
      have hfalse := hp (T1 ∪ T2) (Finset.union_subset hT1J hT2J) (by omega)
      have h1t : l.eval (U ∪ (T1 ∪ T2)) = true :=
        mono_eval_sub J U l hml Finset.subset_union_left (Finset.union_subset hT1J hT2J) hT1e
      have h2t : r.eval (U ∪ (T1 ∪ T2)) = true :=
        mono_eval_sub J U r hmr Finset.subset_union_right (Finset.union_subset hT1J hT2J) hT2e
      simp [SForm.eval, h1t, h2t] at hfalse
    · intro j hj hjv
      simp only [SForm.posVars, Finset.mem_union] at hjv
      rcases hjv with hjl | hjr
      · obtain ⟨T1, hT1J, hjT1, hT1c, hT1e⟩ := (hl2 j hj hjl).1
        obtain ⟨R1, hR1J, hjR1, hR1c, hR1e⟩ := (hl2 j hj hjl).2
        refine ⟨⟨T1 ∪ S2, Finset.union_subset hT1J hS2J, Finset.mem_union_left _ hjT1, ?_, ?_⟩,
          ⟨R1, hR1J, hjR1, hR1c, by simp [SForm.eval, hR1e]⟩⟩
        · have := Finset.card_union_le T1 S2
          omega
        · have h1t : l.eval (U ∪ (T1 ∪ S2)) = true :=
            mono_eval_sub J U l hml Finset.subset_union_left (Finset.union_subset hT1J hS2J) hT1e
          have h2t : r.eval (U ∪ (T1 ∪ S2)) = true :=
            mono_eval_sub J U r hmr Finset.subset_union_right (Finset.union_subset hT1J hS2J) hS2p.2
          simp [SForm.eval, h1t, h2t]
      · obtain ⟨T2, hT2J, hjT2, hT2c, hT2e⟩ := (hr2 j hj hjr).1
        obtain ⟨R2, hR2J, hjR2, hR2c, hR2e⟩ := (hr2 j hj hjr).2
        refine ⟨⟨S1 ∪ T2, Finset.union_subset hS1J hT2J, Finset.mem_union_right _ hjT2, ?_, ?_⟩,
          ⟨R2, hR2J, hjR2, hR2c, by simp [SForm.eval, hR2e]⟩⟩
        · have := Finset.card_union_le S1 T2
          omega
        · have h1t : l.eval (U ∪ (S1 ∪ T2)) = true :=
            mono_eval_sub J U l hml Finset.subset_union_left (Finset.union_subset hS1J hT2J) hS1p.2
          have h2t : r.eval (U ∪ (S1 ∪ T2)) = true :=
            mono_eval_sub J U r hmr Finset.subset_union_right (Finset.union_subset hS1J hT2J) hT2e
          simp [SForm.eval, h1t, h2t]
  | or l r ihl ihr =>
    intro hmono p q hp hq hP
    have hml : Disjoint l.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    have hmr : Disjoint r.negVars J :=
      Finset.disjoint_of_subset_left (by intro x hx; simp [SForm.negVars, hx]) hmono
    by_cases hz : p = 0 ∨ q = 0
    · have h0 : (SForm.or l r).posCount J = 0 := by
        rcases hz with h | h <;> simp [h] at hP <;> exact hP
      have h1 := tight_zero J (SForm.or l r) h0
      exact ⟨h1.1, fun i hi hiv => absurd hiv (h1.2 i hi)⟩
    push_neg at hz
    obtain ⟨hp0, hq0⟩ := hz
    have hpl : ∀ S ⊆ J, S.card < p → l.eval (U ∪ S) = false := by
      intro S hSJ hSc
      have h := hp S hSJ hSc
      simp [SForm.eval] at h; exact h.1
    have hpr : ∀ S ⊆ J, S.card < p → r.eval (U ∪ S) = false := by
      intro S hSJ hSc
      have h := hp S hSJ hSc
      simp [SForm.eval] at h; exact h.2
    let Rl := (J.powerset.filter (fun R => l.eval (U ∪ (J \ R)) = false)).image Finset.card
    let Rr := (J.powerset.filter (fun R => r.eval (U ∪ (J \ R)) = false)).image Finset.card
    have hle : Rl.Nonempty := by
      have hf := hpl ∅ (Finset.empty_subset _) (by simp; omega)
      have heq : J \ J = ∅ := Finset.sdiff_self J
      exact ⟨_, Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, by rwa [heq]⟩, rfl⟩⟩
    have hre : Rr.Nonempty := by
      have hf := hpr ∅ (Finset.empty_subset _) (by simp; omega)
      have heq : J \ J = ∅ := Finset.sdiff_self J
      exact ⟨_, Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, by rwa [heq]⟩, rfl⟩⟩
    let q1 := Rl.min' hle
    let q2 := Rr.min' hre
    have hq1m : q1 ∈ Rl := Finset.min'_mem Rl hle
    have hq2m : q2 ∈ Rr := Finset.min'_mem Rr hre
    obtain ⟨R1, hR1f, hR1c⟩ := Finset.mem_image.mp hq1m
    obtain ⟨R2, hR2f, hR2c⟩ := Finset.mem_image.mp hq2m
    have hR1p := Finset.mem_filter.mp hR1f
    have hR2p := Finset.mem_filter.mp hR2f
    have hR1J : R1 ⊆ J := Finset.mem_powerset.mp hR1p.1
    have hR2J : R2 ⊆ J := Finset.mem_powerset.mp hR2p.1
    have hql : ∀ R ⊆ J, R.card < q1 → l.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      cases hv : l.eval (U ∪ (J \ R)) with
      | true => rfl
      | false =>
        exfalso
        have hmem : R.card ∈ Rl :=
          Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hRJ, hv⟩, rfl⟩
        have hmin := Finset.min'_le Rl R.card hmem
        omega
    have hqr : ∀ R ⊆ J, R.card < q2 → r.eval (U ∪ (J \ R)) = true := by
      intro R hRJ hRc
      cases hv : r.eval (U ∪ (J \ R)) with
      | true => rfl
      | false =>
        exfalso
        have hmem : R.card ∈ Rr :=
          Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hRJ, hv⟩, rfl⟩
        have hmin := Finset.min'_le Rr R.card hmem
        omega
    have hlf : ∀ R R' : Finset (Fin k), R ⊆ R' → R' ⊆ J → l.eval (U ∪ (J \ R)) = false →
        l.eval (U ∪ (J \ R')) = false := by
      intro R R' hRR' _ hf
      cases hv : l.eval (U ∪ (J \ R')) with
      | false => rfl
      | true =>
        have := mono_eval_sub J U l hml (Finset.sdiff_subset_sdiff Finset.Subset.rfl hRR')
          Finset.sdiff_subset hv
        rw [hf] at this; exact absurd this (by decide)
    have hrf : ∀ R R' : Finset (Fin k), R ⊆ R' → R' ⊆ J → r.eval (U ∪ (J \ R)) = false →
        r.eval (U ∪ (J \ R')) = false := by
      intro R R' hRR' _ hf
      cases hv : r.eval (U ∪ (J \ R')) with
      | false => rfl
      | true =>
        have := mono_eval_sub J U r hmr (Finset.sdiff_subset_sdiff Finset.Subset.rfl hRR')
          Finset.sdiff_subset hv
        rw [hf] at this; exact absurd this (by decide)
    have hb1 := mono_pq_bound J U hUJ l hml p q1 hpl hql
    have hb2 := mono_pq_bound J U hUJ r hmr p q2 hpr hqr
    simp only [SForm.posCount] at hP
    have hsum : p * (q1 + q2) ≤ p * q := by rw [Nat.mul_add]; omega
    have hq12 : q1 + q2 ≤ q := Nat.le_of_mul_le_mul_left hsum (by omega)
    have hq_le : q ≤ q1 + q2 := by
      by_contra hgt
      have hcard : (R1 ∪ R2).card < q := by
        have := Finset.card_union_le R1 R2
        omega
      have htrue := hq (R1 ∪ R2) (Finset.union_subset hR1J hR2J) hcard
      have h1 := hlf R1 (R1 ∪ R2) Finset.subset_union_left (Finset.union_subset hR1J hR2J) hR1p.2
      have h2 := hrf R2 (R1 ∪ R2) Finset.subset_union_right (Finset.union_subset hR1J hR2J) hR2p.2
      simp [SForm.eval, h1, h2] at htrue
    have hqeq : q = q1 + q2 := by omega
    have e1 : l.posCount J ≤ p * q1 := by
      have : p * q = p * q1 + p * q2 := by rw [hqeq, Nat.mul_add]
      omega
    have e2 : r.posCount J ≤ p * q2 := by
      have : p * q = p * q1 + p * q2 := by rw [hqeq, Nat.mul_add]
      omega
    obtain ⟨hl1, hl2⟩ := ihl hml p q1 hpl hql e1
    obtain ⟨hr1, hr2⟩ := ihr hmr p q2 hpr hqr e2
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [SForm.posCount]
      by_contra hgt
      have a1 := hl1 j hj
      have a2 := hr1 j hj
      have hjl : j ∈ l.posVars := (SForm.posCount_single_pos l j).mp (by omega)
      have hjr : j ∈ r.posVars := (SForm.posCount_single_pos r j).mp (by omega)
      obtain ⟨T1, hT1J, hjT1, hT1c, hT1e⟩ := (hl2 j hj hjl).2
      obtain ⟨T2, hT2J, hjT2, hT2c, hT2e⟩ := (hr2 j hj hjr).2
      have hinter : 0 < (T1 ∩ T2).card := Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨hjT1, hjT2⟩⟩
      have hcu := Finset.card_union_add_card_inter T1 T2
      have htrue := hq (T1 ∪ T2) (Finset.union_subset hT1J hT2J) (by omega)
      have h1 := hlf T1 (T1 ∪ T2) Finset.subset_union_left (Finset.union_subset hT1J hT2J) hT1e
      have h2 := hrf T2 (T1 ∪ T2) Finset.subset_union_right (Finset.union_subset hT1J hT2J) hT2e
      simp [SForm.eval, h1, h2] at htrue
    · intro j hj hjv
      simp only [SForm.posVars, Finset.mem_union] at hjv
      rcases hjv with hjl | hjr
      · obtain ⟨T1, hT1J, hjT1, hT1c, hT1e⟩ := (hl2 j hj hjl).1
        obtain ⟨Q1, hQ1J, hjQ1, hQ1c, hQ1e⟩ := (hl2 j hj hjl).2
        refine ⟨⟨T1, hT1J, hjT1, hT1c, by simp [SForm.eval, hT1e]⟩,
          ⟨Q1 ∪ R2, Finset.union_subset hQ1J hR2J, Finset.mem_union_left _ hjQ1, ?_, ?_⟩⟩
        · have := Finset.card_union_le Q1 R2
          omega
        · have h1 := hlf Q1 (Q1 ∪ R2) Finset.subset_union_left (Finset.union_subset hQ1J hR2J) hQ1e
          have h2 := hrf R2 (Q1 ∪ R2) Finset.subset_union_right (Finset.union_subset hQ1J hR2J) hR2p.2
          simp [SForm.eval, h1, h2]
      · obtain ⟨T2, hT2J, hjT2, hT2c, hT2e⟩ := (hr2 j hj hjr).1
        obtain ⟨Q2, hQ2J, hjQ2, hQ2c, hQ2e⟩ := (hr2 j hj hjr).2
        refine ⟨⟨T2, hT2J, hjT2, hT2c, by simp [SForm.eval, hT2e]⟩,
          ⟨R1 ∪ Q2, Finset.union_subset hR1J hQ2J, Finset.mem_union_right _ hjQ2, ?_, ?_⟩⟩
        · have := Finset.card_union_le R1 Q2
          omega
        · have h1 := hlf R1 (R1 ∪ Q2) Finset.subset_union_left (Finset.union_subset hR1J hQ2J) hR1p.2
          have h2 := hrf Q2 (R1 ∪ Q2) Finset.subset_union_right (Finset.union_subset hR1J hQ2J) hQ2e
          simp [SForm.eval, h1, h2]

lemma core2 {k : Nat} (F : SForm k) (A B : Finset (Fin k)) (q : Nat) (hq : 0 < q) (hAB : A ⊆ B)
    (hprot : ∀ Y, A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < 2 → F.eval Y = false) ∧ ((B \ Y).card < q → F.eval Y = true))) :
    2 * q ≤ F.posCount (B \ A) + F.negCount (B \ A) ∧
    (F.posCount (B \ A) + F.negCount (B \ A) ≤ 2 * q →
      F.posCount (B \ A) = 2 * q ∧ F.negCount (B \ A) = 0 ∧
      (∀ j ∈ B \ A, F.posCount {j} ≤ 1) ∧
      ((B \ A).filter (fun j => F.posCount {j} = 1 ∧ F.negCount {j} = 0)).card = 2 * q) := by
  set H := B \ A with hH
  suffices key : F.posCount H + F.negCount H ≤ 2 * q →
      F.posCount H = 2 * q ∧ F.negCount H = 0 ∧
      (∀ j ∈ H, F.posCount {j} ≤ 1) ∧
      (H.filter (fun j => F.posCount {j} = 1 ∧ F.negCount {j} = 0)).card = 2 * q by
    refine ⟨?_, key⟩
    by_contra hlt
    push_neg at hlt
    have := (key hlt.le).1
    omega
  intro hL
  have hHA : Disjoint A H := by rw [hH]; exact Finset.disjoint_sdiff
  have hHB : H ⊆ B := Finset.sdiff_subset
  set V := H ∩ (F.posVars ∪ F.negVars) with hVdef
  set Mx := H ∩ (F.posVars ∩ F.negVars) with hMxdef
  have hVH : V ⊆ H := Finset.inter_subset_left
  have hMH : Mx ⊆ H := Finset.inter_subset_left
  have hV : q + 1 ≤ V.card := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨S', hS'V, hS'1, hS'q⟩ : ∃ S' ⊆ V, S'.card < 2 ∧ (V \ S').card < q := by
      rcases V.eq_empty_or_nonempty with he | ⟨v, hv⟩
      · exact ⟨∅, Finset.empty_subset _, by simp, by rw [he]; simp; omega⟩
      · refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp, ?_⟩
        have := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hv)
        simp at this
        omega
    have hS'H : S' ⊆ H := Finset.Subset.trans hS'V hVH
    have hAS : Disjoint A S' := Finset.disjoint_of_subset_right hS'H hHA
    have e1 : F.eval (A ∪ S') = false := by
      refine (hprot (A ∪ S') Finset.subset_union_left
        (Finset.union_subset hAB (Finset.Subset.trans hS'H hHB))).1 ?_
      rw [Finset.union_sdiff_cancel_left hAS]; exact hS'1
    have hVS'B : V \ S' ⊆ B := Finset.Subset.trans Finset.sdiff_subset (Finset.Subset.trans hVH hHB)
    have e2 : F.eval (B \ (V \ S')) = true := by
      refine (hprot (B \ (V \ S')) ?_ Finset.sdiff_subset).2 ?_
      · intro x hx
        refine Finset.mem_sdiff.mpr ⟨hAB hx, fun h => ?_⟩
        exact Finset.disjoint_left.mp hHA hx (hVH (Finset.mem_sdiff.mp h).1)
      · rw [Finset.sdiff_sdiff_eq_self hVS'B]; exact hS'q
    have heq : F.eval (A ∪ S') = F.eval (B \ (V \ S')) := by
      apply SForm.eval_congr_vars
      intro j hj
      constructor
      · intro h
        rcases Finset.mem_union.mp h with hA | hS
        · refine Finset.mem_sdiff.mpr ⟨hAB hA, fun h' => ?_⟩
          exact Finset.disjoint_left.mp hHA hA (hVH (Finset.mem_sdiff.mp h').1)
        · refine Finset.mem_sdiff.mpr ⟨hHB (hS'H hS), fun h' => (Finset.mem_sdiff.mp h').2 hS⟩
      · intro h
        obtain ⟨hB, hn⟩ := Finset.mem_sdiff.mp h
        by_cases hjA : j ∈ A
        · exact Finset.mem_union_left _ hjA
        · have hjH : j ∈ H := by rw [hH]; exact Finset.mem_sdiff.mpr ⟨hB, hjA⟩
          have hjV : j ∈ V := Finset.mem_inter.mpr ⟨hjH, Finset.mem_union.mpr hj⟩
          refine Finset.mem_union_right _ ?_
          by_contra hc
          exact hn (Finset.mem_sdiff.mpr ⟨hjV, hc⟩)
    rw [e1, e2] at heq
    exact absurd heq (by decide)
  have hP1 := SForm.posCount_ge_card_inter_posVars H F
  have hN1 := SForm.negCount_ge_card_inter_negVars H F
  have hcu := Finset.card_union_add_card_inter (H ∩ F.posVars) (H ∩ F.negVars)
  have hU : (H ∩ F.posVars) ∪ (H ∩ F.negVars) = V := (Finset.inter_union_distrib_left _ _ _).symm
  have hI : (H ∩ F.posVars) ∩ (H ∩ F.negVars) = Mx := by
    ext x; simp only [Finset.mem_inter, hMxdef]; tauto
  rw [hU, hI] at hcu
  have hr : Mx.card < q := by omega
  have hb := pin_bound F A B H 2 q hAB hH hprot F.andConf (Or.inl rfl) Mx 0
    (by
      intro x hx
      obtain ⟨hxH, hxT⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxH, Finset.mem_inter.mpr
        ⟨SForm.andConf_sub_posVars F hxT, SForm.andConf_sub_negVars F hxT⟩⟩)
    hMH (Nat.zero_le _) (by norm_num) (by omega)
  simp only [Nat.sub_zero] at hb
  have sP : F.posCount H = F.posCount (H \ Mx) + F.posCount Mx := by
    have h := SForm.posCount_add_disjoint (A := H \ Mx) (B := Mx) Finset.sdiff_disjoint F
    rwa [Finset.sdiff_union_of_subset hMH] at h
  have sN : F.negCount H = F.negCount (H \ Mx) + F.negCount Mx := by
    have h := SForm.negCount_add_disjoint (A := H \ Mx) (B := Mx) Finset.sdiff_disjoint F
    rwa [Finset.sdiff_union_of_subset hMH] at h
  have hMpos : Mx ⊆ F.posVars := fun x hx => (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1
  have hMneg : Mx ⊆ F.negVars := fun x hx => (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2
  have pM : Mx.card ≤ F.posCount Mx := by
    have h := SForm.posCount_ge_card_inter_posVars Mx F
    rwa [Finset.inter_eq_left.mpr hMpos] at h
  have nM : Mx.card ≤ F.negCount Mx := by
    have h := SForm.negCount_ge_card_inter_negVars Mx F
    rwa [Finset.inter_eq_left.mpr hMneg] at h
  have hr0 : Mx = ∅ := by
    by_contra hne
    obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty hne
    have hmMs : ({m} : Finset (Fin k)) ⊆ Mx := Finset.singleton_subset_iff.mpr hm
    have hcm := Finset.card_sdiff_add_card_eq_card hmMs
    simp only [Finset.card_singleton] at hcm
    have hmP : F.posCount {m} ≤ 1 := by
      have s := SForm.posCount_split F hm
      have h := SForm.posCount_ge_card_inter_posVars (Mx \ {m}) F
      rw [Finset.inter_eq_left.mpr (Finset.Subset.trans Finset.sdiff_subset hMpos)] at h
      omega
    have hmN : F.negCount {m} ≤ 1 := by
      have s := SForm.negCount_split F hm
      have h := SForm.negCount_ge_card_inter_negVars (Mx \ {m}) F
      rw [Finset.inter_eq_left.mpr (Finset.Subset.trans Finset.sdiff_subset hMneg)] at h
      omega
    obtain ⟨T, hT, hmT, hTsub⟩ : ∃ T : Finset (Fin k), (T = F.andConf ∨ T = F.orConf) ∧ m ∉ T ∧
        T ⊆ F.posVars ∩ F.negVars := by
      by_cases hma : m ∈ F.andConf
      · refine ⟨F.orConf, Or.inr rfl, SForm.conf_unique m F hmP hmN hma, ?_⟩
        intro x hx
        exact Finset.mem_inter.mpr ⟨SForm.orConf_sub_posVars F hx, SForm.orConf_sub_negVars F hx⟩
      · refine ⟨F.andConf, Or.inl rfl, hma, ?_⟩
        intro x hx
        exact Finset.mem_inter.mpr ⟨SForm.andConf_sub_posVars F hx, SForm.andConf_sub_negVars F hx⟩
    have hKH : Mx \ {m} ⊆ H := Finset.Subset.trans Finset.sdiff_subset hMH
    have hb2 := pin_bound F A B H 2 q hAB hH hprot T hT (Mx \ {m}) 0
      (by
        intro x hx
        obtain ⟨hxH, hxT⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hxH, hTsub hxT⟩, ?_⟩
        intro hxm
        rw [Finset.mem_singleton] at hxm
        subst hxm
        exact hmT hxT)
      hKH (Nat.zero_le _) (by norm_num) (by omega)
    simp only [Nat.sub_zero] at hb2
    have hmHK : m ∈ H \ (Mx \ {m}) := by
      refine Finset.mem_sdiff.mpr ⟨hMH hm, fun h => ?_⟩
      exact (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self m)
    have s2 := SForm.posCount_split F hmHK
    have hset : (H \ (Mx \ {m})) \ ({m} : Finset (Fin k)) = H \ Mx := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hxH, hxn⟩, hxm⟩
        exact ⟨hxH, fun hxM => hxn ⟨hxM, hxm⟩⟩
      · rintro ⟨hxH, hxM⟩
        refine ⟨⟨hxH, fun h => hxM h.1⟩, ?_⟩
        rintro rfl
        exact hxM hm
    rw [hset] at s2
    omega
  have hMc : Mx.card = 0 := by rw [hr0]; rfl
  have hPH : F.posCount H = 2 * q := by omega
  have hNH : F.negCount H = 0 := by omega
  have hdis : Disjoint F.negVars H := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact Finset.card_eq_zero.mp (by omega)
  have hS : ∀ S ⊆ H, S.card < 2 → F.eval (A ∪ S) = false := by
    intro S hSH hSc
    have hAS : Disjoint A S := Finset.disjoint_of_subset_right hSH hHA
    refine (hprot (A ∪ S) Finset.subset_union_left
      (Finset.union_subset hAB (Finset.Subset.trans hSH hHB))).1 ?_
    rw [Finset.union_sdiff_cancel_left hAS]; exact hSc
  have hR : ∀ R ⊆ H, R.card < q → F.eval (A ∪ (H \ R)) = true := by
    intro R hRH hRc
    refine (hprot (A ∪ (H \ R)) Finset.subset_union_left
      (Finset.union_subset hAB (Finset.Subset.trans Finset.sdiff_subset hHB))).2 ?_
    have : B \ (A ∪ (H \ R)) = R := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, hH]
      constructor
      · rintro ⟨hxB, hxn⟩
        by_contra hxR
        exact hxn (by
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · exact Or.inr ⟨⟨hxB, hxA⟩, hxR⟩)
      · intro hxR
        have hx := hRH hxR
        rw [hH] at hx
        obtain ⟨hxB, hxA⟩ := Finset.mem_sdiff.mp hx
        refine ⟨hxB, ?_⟩
        rintro (h | h)
        · exact hxA h
        · exact h.2 hxR
    rw [this]; exact hRc
  have ht := mono_tight H A hHA F hdis 2 q hS hR (by omega)
  refine ⟨hPH, hNH, ht.1, ?_⟩
  have hN0 : ∀ j ∈ H, F.negCount {j} = 0 := by
    intro j hj
    have := SForm.negCount_mono F (Finset.singleton_subset_iff.mpr hj)
    omega
  rw [Finset.card_filter, ← hPH, SForm.posCount_sum F H]
  apply Finset.sum_congr rfl
  intro j hj
  have h1 := ht.1 j hj
  have h2 := hN0 j hj
  by_cases hj1 : F.posCount {j} = 1
  · simp [hj1, h2]
  · have : F.posCount {j} = 0 := by omega
    simp [this]

def SForm.dual {k : Nat} : SForm k → SForm k
  | .const b => .const (!b)
  | .lit j pol => .lit j pol
  | .and l r => .or l.dual r.dual
  | .or l r => .and l.dual r.dual

lemma SForm.eval_dual {k : Nat} (Y : Finset (Fin k)) (F : SForm k) :
    F.dual.eval Y = !(F.eval (Finset.univ \ Y)) := by
  induction F with
  | const b => simp [SForm.dual, SForm.eval]
  | lit j pol => cases pol <;> simp [SForm.dual, SForm.eval]
  | and l r ihl ihr => simp [SForm.dual, SForm.eval, ihl, ihr]
  | or l r ihl ihr => simp [SForm.dual, SForm.eval, ihl, ihr]

lemma SForm.posCount_dual {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.dual.posCount J = F.posCount J := by
  induction F with
  | const b => rfl
  | lit j pol => rfl
  | and l r ihl ihr => simp [SForm.dual, SForm.posCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.dual, SForm.posCount, ihl, ihr]

lemma SForm.negCount_dual {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.dual.negCount J = F.negCount J := by
  induction F with
  | const b => rfl
  | lit j pol => rfl
  | and l r ihl ihr => simp [SForm.dual, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.dual, SForm.negCount, ihl, ihr]

lemma core_both {k : Nat} (F : SForm k) (A B : Finset (Fin k)) (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hpq : p = 2 ∨ q = 2) (hAB : A ⊆ B)
    (hprot : ∀ Y, A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < p → F.eval Y = false) ∧ ((B \ Y).card < q → F.eval Y = true))) :
    p * q ≤ F.posCount (B \ A) + F.negCount (B \ A) ∧
    (F.posCount (B \ A) + F.negCount (B \ A) ≤ p * q →
      F.posCount (B \ A) = p * q ∧ F.negCount (B \ A) = 0 ∧
      (∀ j ∈ B \ A, F.posCount {j} ≤ 1) ∧
      ((B \ A).filter (fun j => F.posCount {j} = 1 ∧ F.negCount {j} = 0)).card = p * q) := by
  rcases hpq with rfl | rfl
  · exact core2 F A B q hq hAB hprot
  · let A' := Finset.univ \ B
    let B' := Finset.univ \ A
    have hAB' : A' ⊆ B' := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hAB
    have hH' : B' \ A' = B \ A := by
      ext x; simp [A', B']; tauto
    have hprot' : ∀ Y, A' ⊆ Y → Y ⊆ B' →
        (((Y \ A').card < 2 → F.dual.eval Y = false) ∧ ((B' \ Y).card < p → F.dual.eval Y = true)) := by
      intro Y h1 h2
      have hA : A ⊆ Finset.univ \ Y := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hxY
        have := h2 hxY
        simp [B', hx] at this
      have hB : Finset.univ \ Y ⊆ B := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
        by_contra hxB
        exact hx (h1 (by simp [A', hxB]))
      have e1 : Y \ A' = B \ (Finset.univ \ Y) := by
        ext x; simp [A']; tauto
      have e2 : B' \ Y = (Finset.univ \ Y) \ A := by
        ext x; simp [B']; tauto
      have hpr := hprot (Finset.univ \ Y) hA hB
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · rw [e1] at hc
        rw [SForm.eval_dual, hpr.2 hc]; rfl
      · rw [e2] at hc
        rw [SForm.eval_dual, hpr.1 hc]; rfl
    have hc := core2 F.dual A' B' p hp hAB' hprot'
    rw [hH'] at hc
    simp only [SForm.posCount_dual, SForm.negCount_dual] at hc
    rw [Nat.mul_comm p 2]
    exact hc

end PEqualNP.Outside.L_lib_1466_aux

theorem PEqualNP.Outside.L_lib_1466 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let occ := fun {k : Nat} (J : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let xs := List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0,0),(0,0)]
  let ws := D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0,0)
      (acc.1+z.1,acc.2+z.2)) (0,0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
    zs ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else ab]) xs
  ws.getD D.output (0,0)
let protects := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset (Fin k)) (p q : Nat) =>
  ∀ Y, A ⊆ Y → Y ⊆ B → (((Y \ A).card < p → run D Y=false) ∧ ((B \ Y).card < q → run D Y=true))
∀ (k p q : Nat) (A B : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit),
  0<p → 0<q → (p=2 ∨ q=2) → A ⊆ B → valid k D → protects D A B p q →
  let H := B \ A
  let count := occ H D
  p*q ≤ count.1+count.2 ∧
  (count.1+count.2 ≤ p*q → count=(p*q,0) ∧
    (∀ j ∈ H, (occ {j} D).1 ≤ 1) ∧
    (H.filter (fun j => occ {j} D=(1,0))).card=p*q)) := by
  intro valid run occ protects k p q A B D hp0 hq0 hpq hAB hval hprot H count
  obtain ⟨F, hFeval, hFcnt, _⟩ := PEqualNP.Outside.L_lib_1466_aux.unfold_circuit (k := k) D hval.1
  have hprotF : ∀ Y, A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < p → F.eval Y = false) ∧ ((B \ Y).card < q → F.eval Y = true)) := by
    intro Y h1 h2
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hFeval]; exact (hprot Y h1 h2).1 (by convert hc)
    · rw [hFeval]; exact (hprot Y h1 h2).2 (by convert hc)
  have hc := PEqualNP.Outside.L_lib_1466_aux.core_both F A B p q hp0 hq0 hpq hAB hprotF
  have hHe : H = B \ A := by ext x; simp [H]
  have hocc : ∀ J : Finset (Fin k), occ J D = (F.posCount J, F.negCount J) := fun J => (hFcnt J).symm
  have hcount : count = (F.posCount (B \ A), F.negCount (B \ A)) := by
    rw [← hHe]; exact hocc H
  rw [hcount]
  simp only [hocc]
  refine ⟨hc.1, fun hle => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hc.2 hle
  refine ⟨by rw [h1, h2], fun j hj => h3 j (by rw [← hHe]; exact hj), ?_⟩
  rw [← h4, hHe]
  simp only [Prod.mk.injEq]
