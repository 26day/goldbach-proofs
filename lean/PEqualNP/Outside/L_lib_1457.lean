import PEqualNP.Defs
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_lib_1457.Core.CoverCircuit
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

end PEqualNP.Outside.L_lib_1457.Core.CoverCircuit

namespace PEqualNP.Outside.L_lib_1457.Core.FiniteGateBank

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1457.Core.CoverCircuit (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

structure Net (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n+j

def empty (n : Nat) : Net n := ⟨[],by simp [FanInTwo],by simp⟩

def Net.cost (p : Net n) := NotBracket.notCount ⟨p.gates,0⟩

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) :=
  ∃ i, i < n+p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size neg : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length+size ∧ q.cost=p.cost+neg

theorem start (raw : X → List Bool) (p : Net n) : Grow raw p p 0 0 := by simp [Grow]

theorem chain {raw : X → List Bool} {p q r : Net n} {a b c d : Nat}
    (pq : Grow raw p q a b) (qr : Grow raw q r c d) : Grow raw p r (a+c) (b+d) :=
  ⟨fun f h => qr.1 f (pq.1 f h),by have := pq.2.1; have := qr.2.1; omega,
    by rw [qr.2.2,pq.2.2,Nat.add_assoc]⟩

theorem allowance {raw : X → List Bool} {p q : Net n} {a b c : Nat}
    (grow : Grow raw p q a b) (le : a≤c) : Grow raw p q c b :=
  ⟨grow.1,grow.2.1.trans (Nat.add_le_add_left le _),grow.2.2⟩

private def extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n where
  gates := p.gates++[g]
  fan := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j=p.gates.length := by simp at hj; omega
      subst j
      simp at hi
      exact ok i hi

private theorem emit {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) :
    ∃ q, Grow raw p q 1 (if g.op=.not then 1 else 0) ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := extend p g ops ok
  have len (x : X) : (run p.gates (raw x)).length=n+p.gates.length := by rw [run_length,width]
  refine ⟨q,⟨?_,by simp [q,extend],?_⟩,n+p.gates.length,by simp [q,extend],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,List.filter_append,List.length_append]
    split <;> simp_all
  · intro x
    change (run (p.gates++[g]) (raw x)).getD (n+p.gates.length) false = _
    rw [run_append,run_singleton,←len x]; simp

theorem binary {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a b : X → Bool) (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q, Grow raw p q 1 0 ∧ q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨i,hi,readI⟩ := ha
  obtain ⟨j,hj,readJ⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or,[i,j]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by cases isAnd <;> simp [g]) (by simp [g,hi,hj])
  refine ⟨q,by cases isAnd <;> simpa [g] using grow,?_⟩
  convert w using 2 with x
  cases isAnd <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    PEqualNP.Outside.L_lib_1457.Core.CoverCircuit.eval_and2,PEqualNP.Outside.L_lib_1457.Core.CoverCircuit.eval_or2, readI,readJ] <;> rfl

theorem invert {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a : X → Bool) (ha : p.has raw a) :
    ∃ q, Grow raw p q 1 1 ∧ q.has raw (fun x => !(a x)) := by
  obtain ⟨i,hi,readI⟩ := ha
  let g : Gate := ⟨.not,[i]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by simp [g]) (by simp [g,hi])
  refine ⟨q,by simpa [g] using grow,?_⟩
  convert w using 2 with x
  change (!(a x)) = (!((run p.gates (raw x)).getD i false))
  rw [readI]

theorem anyList {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,zero⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old false
    exact ⟨r,chain gq gr,by simpa [List.any_cons] using ans⟩

theorem batch {raw : X → List Bool} (p : Net n) (l : List J) (f : J → X → Bool) (s z : Nat)
    (build : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r, Grow raw q r s z ∧ r.has raw (f j)) :
    ∃ r, Grow raw p r (l.length*s) (l.length*z) ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p,by simpa using start raw p,by simp⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => build i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := build j (by simp) q gq.1
    refine ⟨r,by simpa [Nat.succ_mul] using chain gq gr,?_⟩
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact ans
    · exact gr.1 _ (old i h)

theorem Net.readsBack (p : Net n) : ReadsBack n ⟨p.gates,0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi)

end PEqualNP.Outside.L_lib_1457.Core.FiniteGateBank

namespace PEqualNP.Outside.L_lib_1457.Core.LowMergeProof

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

theorem wires_mono (C : Circuit) (hC : IsMonotoneCircuit C) (a b : List Bool)
    (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

end PEqualNP.Outside.L_lib_1457.Core.LowMergeProof

namespace PEqualNP.Outside.L_lib_1457.Core.GraphInversionSeeds

abbrev I (n : Nat) := Fin n
abbrev Edge (n : Nat) := I n × I n
abbrev F (n : Nat) := (I n → Bool) → Bool

abbrev pos (i : I n) : F n := fun x => x i
abbrev neg (i : I n) : F n := fun x => !(x i)
abbrev eqBit (e : Edge n) : F n := fun x => x e.1 == x e.2
abbrev xorBit (e : Edge n) : F n := fun x => xor (x e.1) (x e.2)
abbrev zz (e : Edge n) : F n := fun x => !(x e.1) && !(x e.2)
abbrev oz (e : Edge n) : F n := fun x => x e.1 && !(x e.2)
abbrev zo (e : Edge n) : F n := fun x => !(x e.1) && x e.2

noncomputable def raw (E : Finset (Edge n)) : Finset (F n) := by
  classical
  exact {fun _ => false,fun _ => true} ∪ Finset.univ.image pos ∪ E.image eqBit ∪ E.image xorBit
noncomputable def target (E : Finset (Edge n)) : Finset (F n) := by
  classical
  exact Finset.univ.image neg ∪ E.image zz ∪ E.image oz ∪ E.image zo

private abbrev bAnd {X : Type} (x y : X → Bool) : X → Bool := fun a => x a && y a
private abbrev bOr {X : Type} (x y : X → Bool) : X → Bool := fun a => x a || y a

def hits (E : Finset (Edge n)) (S : Finset (I n)) : Prop :=
  ∀ C : Finset (I n), C.Nonempty → (∀ e∈E, e.1∈C ↔ e.2∈C) →
    ∃ i∈C, i∈S

def sampleStep {X : Type} (U : Finset (X → Bool)) (z : X → Bool) : Prop :=
  ∃ x∈U, ∃ y∈U, z=bAnd x y ∨ z=bOr x y

abbrev Step (U : Finset (F n)) (z : F n) := sampleStep U z

theorem grow (E : Finset (Edge n)) (S : Finset (I n))
    (D U : Finset (F n)) (cover : hits E S) (rawIn : raw E ⊆ U)
    (targetIn : target E ⊆ D) (seeds : ∀ i∈S, neg i∈U)
    (stable : ∀ z∈D, Step U z → z∈U) : target E ⊆ U := by
  classical
  have input (i : I n) : pos i∈U := rawIn (by simp [raw])
  have same (e) (he : e∈E) : eqBit e∈U := rawIn (by simp only [raw,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))
  have diff (e) (he : e∈E) : xorBit e∈U := rawIn (by simp only [raw,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ he))
  have mkAnd {x y z : F n} (hx : x∈U) (hy : y∈U) (hz : z∈target E)
      (eq : z=bAnd x y) : z∈U := stable z (targetIn hz) ⟨x,hx,y,hy,Or.inl eq⟩
  have mkOr {x y z : F n} (hx : x∈U) (hy : y∈U) (hz : z∈target E)
      (eq : z=bOr x y) : z∈U := stable z (targetIn hz) ⟨x,hx,y,hy,Or.inr eq⟩
  have first (e) (he : e∈E) : oz e∈U :=
    mkAnd (input e.1) (diff e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [oz,pos,bAnd,xorBit,h,k])
  have second (e) (he : e∈E) : zo e∈U :=
    mkAnd (input e.2) (diff e he) (by simp only [target,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ he)) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zo,pos,bAnd,xorBit,h,k])
  have zeroLeft (e) (he : e∈E) (hi : neg e.1∈U) : zz e∈U :=
    mkAnd hi (same e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zz,neg,bAnd,eqBit,h,k])
  have zeroRight (e) (he : e∈E) (hi : neg e.2∈U) : zz e∈U :=
    mkAnd hi (same e he) (by simp only [target,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))) (by
      funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [zz,neg,bAnd,eqBit,h,k])
  have spread (e) (he : e∈E) : neg e.1∈U ↔ neg e.2∈U := by
    constructor
    · intro h
      exact mkOr (zeroLeft e he h) (first e he) (by simp [target]) (by
        funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [neg,bOr,zz,oz,h,k])
    · intro h
      exact mkOr (zeroRight e he h) (second e he) (by simp [target]) (by
        funext x; cases h : x e.1 <;> cases k : x e.2 <;> simp [neg,bOr,zz,zo,h,k])
  have all (i : I n) : neg i∈U := by
    by_contra absent
    let C := Finset.univ.filter (fun j : I n => neg j∉U)
    have mem (j) : j∈C ↔ neg j∉U := by simp [C]
    obtain ⟨j,hj,hs⟩ := cover C ⟨i,(mem i).mpr absent⟩
      (fun e he => (mem _).trans ((not_congr (spread e he)).trans (mem _).symm))
    exact (mem j).mp hj (seeds j hs)
  intro z hz
  simp only [target,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with (((⟨i,rfl⟩|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
  · exact all _
  · exact zeroLeft e he (all _)
  · exact first _ he
  · exact second _ he

private theorem obstruction (E : Finset (Edge n)) (S C : Finset (I n))
    (closed : ∀ e∈E, e.1∈C ↔ e.2∈C) (miss : ∀ i∈C, i∉S) :
    ∃ a b : I n → Bool,
      (∀ z∈raw E, z a = true → z b = true) ∧
      (∀ i∈S, neg i a = true → neg i b = true) ∧
      ∀ i∈C, neg i a = true ∧ neg i b = false := by
  classical
  let b := fun i => decide (i∈C)
  have agree (e) (he : e∈E) : b e.1=b e.2 := by simp [b,closed e he]
  refine ⟨fun _ => false,b,?_,?_,?_⟩
  · intro z hz
    simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_univ,true_and] at hz
    rcases hz with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
    · simp
    · simp
    · simp [pos]
    · simp [eqBit,agree e he]
    · simp [xorBit]
  · intro i hi
    have out : i∉C := fun h => miss i h hi
    simp [neg,b,out]
  · intro i hi
    simp [neg,b,hi]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_lib_1457.Core.FiniteGateBank
open Classical

abbrev sampleRow {X : Type} (L : List (X → Bool)) (x : X) := L.map (fun f => f x)
def sampleFits {X : Type} (L : List (X → Bool)) (T : Finset (X → Bool)) (p : Nat) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧
    C.output < L.length+C.size ∧ C.size≤p ∧
    ∀ f∈T, ∃ i<L.length+C.size, ∀ x, (C.wires (sampleRow L x)).getD i false=f x

private theorem emitAll {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool))
    (closed : ∀ U, L.toFinset⊆U → (∀ z∈T, sampleStep U z → z∈U) → T⊆U)
    (U : Finset (X → Bool)) (base : L.toFinset⊆U) (net : Net L.length)
    (live : ∀ f∈U, net.has (sampleRow L) f) :
    ∃ net' : Net L.length, net'.cost=net.cost ∧ net'.gates.length≤net.gates.length+(T\U).card ∧
      ∀ f∈T, net'.has (sampleRow L) f := by
  by_cases doneT : T⊆U
  · exact ⟨net,rfl,by omega,fun f hf => live f (doneT hf)⟩
  have advance : ∃ z∈T, z∉U ∧ sampleStep U z := by
    by_contra! none
    exact doneT (closed U base (fun z hz step => by by_contra h; exact none z hz h step))
  obtain ⟨z,hz,fresh,x,hx,y,hy,op⟩ := advance
  have build : ∃ q, Grow (sampleRow L) net q 1 0 ∧ q.has (sampleRow L) z := by
    rcases op with rfl|rfl
    · simpa only [if_true] using binary (raw := sampleRow L) (fun _ => by simp [sampleRow]) net x y (live x hx) (live y hy) true
    · simpa only [Bool.false_eq_true,if_false] using binary (raw := sampleRow L) (fun _ => by simp [sampleRow]) net x y (live x hx) (live y hy) false
  obtain ⟨q,progress,hzq⟩ := build
  have diff : T \ insert z U=(T\U).erase z := by ext i; simp; tauto
  have one : (T\insert z U).card+1=(T\U).card := by
    rw [diff]; exact Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hz,fresh⟩)
  obtain ⟨r,hr,size,done⟩ := emitAll L T closed (insert z U) (base.trans (Finset.subset_insert _ _)) q
    (fun v hv => (Finset.mem_insert.mp hv).elim (fun eq => eq ▸ hzq) (fun h => progress.1 _ (live v h)))
  exact ⟨r,by simpa [progress.2.2] using hr,by have inc := progress.2.1; omega,done⟩
termination_by (T\U).card

theorem tightBuild {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool)) (nonempty : 0<L.length)
    (closed : ∀ U, L.toFinset⊆U → (∀ z∈T, sampleStep U z → z∈U) → T⊆U) :
    sampleFits L T (T\L.toFinset).card := by
  have base (f) (hf : f∈L.toFinset) : (empty L.length).has (sampleRow L) f := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hf)
    refine ⟨i,by simpa [empty] using hi,?_⟩
    intro x
    change (sampleRow L x).getD i false = f x
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa [sampleRow] using congrFun he x
  obtain ⟨q,cost,size,all⟩ := emitAll L T closed L.toFinset (by rfl) (empty L.length) base
  let C : Circuit := ⟨q.gates,0⟩
  have no : (C.gates.filter (fun g => decide (g.op=GateOp.not)))=[] := by
    apply List.length_eq_zero_iff.mp
    simpa [C,Net.cost,NotBracket.notCount,empty] using cost
  have positive : Monotone2 C := by
    intro g hg
    have types := q.fan g hg
    have hn : g.op ≠ GateOp.not := by
      intro bad
      have h : g∈C.gates.filter (fun t => decide (t.op=GateOp.not)) := by simp [hg,bad]
      rw [no] at h
      simp at h
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff,hn] using types
  exact ⟨C,positive,q.readsBack,by change 0<L.length+_; omega,by simpa [C,Circuit.size,empty] using size,all⟩

theorem countMissing {X : Type} [DecidableEq (X → Bool)] (L : List (X → Bool)) (T : Finset (X → Bool)) {p} (h : sampleFits L T p) :
    (T\L.toFinset).card≤p := by
  obtain ⟨C,_,_,_,size,all⟩ := h
  let added (j : Fin C.size) : X → Bool := fun x => (C.wires (sampleRow L x)).getD (L.length+j.val) false
  have sub : T\L.toFinset ⊆ Finset.univ.image added := by
    intro f hf
    obtain ⟨present,missing⟩ := Finset.mem_sdiff.mp hf
    obtain ⟨i,hi,he⟩ := all f present
    by_cases input : i<L.length
    · have eq : L[i]=f := by
        funext x
        obtain ⟨tail,old,_⟩ := CoverCircuit.run_prefix C.gates (sampleRow L x)
        have q := he x
        rw [CoverCircuit.wires_eq,old,List.getD_append _ _ _ _ (by simpa using input),
          List.getD_eq_getElem _ _ (by simpa using input)] at q
        simpa [sampleRow] using q
      exact False.elim (missing (List.mem_toFinset.mpr (eq ▸ List.getElem_mem input)))
    · refine Finset.mem_image.mpr ⟨⟨i-L.length,by omega⟩,Finset.mem_univ _,?_⟩
      funext x
      simpa [added,show L.length+(i-L.length)=i by omega] using he x
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le.trans (by simp)).trans size)

abbrev row (L : List (F n)) (x : I n → Bool) := sampleRow L x
abbrev fits (L : List (F n)) (T : Finset (F n)) (p : Nat) := sampleFits L T p

private theorem lower (E : Finset (Edge n)) (S : Finset (I n)) (L : List (F n))
    (inputs : L.toFinset=raw E ∪ S.image neg) {p} (fit : fits L (target E) p) : hits E S := by
  intro C nonempty closed
  by_contra! miss
  obtain ⟨a,b,base,seed,drops⟩ := obstruction E S C closed miss
  obtain ⟨D,mono,_,_,_,reads⟩ := fit
  have ordered : LowMergeProof.LeL (row L a) (row L b) := by
    intro i
    by_cases h : i<L.length
    · simp only [row,List.getD_eq_getElem _ _ (by simpa using h : i<(row L a).length),
        List.getD_eq_getElem _ _ (by simpa using h : i<(row L b).length), List.getElem_map]
      have mem : L[i]∈raw E ∪ S.image neg := inputs ▸ List.mem_toFinset.mpr (List.getElem_mem h)
      rcases Finset.mem_union.mp mem with hr|hs
      · exact base _ hr
      · obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hs
        rw [←eq]
        exact seed j hj
    · simp [row,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]
  obtain ⟨i,hi⟩ := nonempty
  obtain ⟨j,_,read⟩ := reads (neg i) (by simp [target])
  have m := LowMergeProof.wires_mono D (fun g hg => (mono g hg).1) (row L a) (row L b) (by simp) ordered j
  rw [read a,read b,(drops i hi).1,(drops i hi).2] at m
  simp at m

theorem exactBudget (E : Finset (Edge n)) (S : Finset (I n)) (L : List (F n))
    (inputs : L.toFinset=raw E ∪ S.image neg) (p : Nat) :
    fits L (target E) p ↔ hits E S ∧ ((target E)\L.toFinset).card≤p := by
  refine ⟨fun h => ⟨lower E S L inputs h,countMissing (X:=I n → Bool) L (target E) h⟩,?_⟩
  rintro ⟨cover,budget⟩
  have nonempty : 0<L.length := by
    obtain ⟨f,hf⟩ : L.toFinset.Nonempty := ⟨fun _ => false,by rw [inputs]; simp [raw]⟩
    exact List.length_pos_of_mem (List.mem_toFinset.mp hf)
  obtain ⟨D,hm,hr,ho,sz,all⟩ := tightBuild L (target E) nonempty (by
    intro U hU stable
    rw [inputs] at hU
    exact grow E S (target E) U cover (Finset.union_subset_iff.mp hU).1 (by rfl)
      (fun i hi => (Finset.union_subset_iff.mp hU).2 (Finset.mem_image_of_mem _ hi)) stable)
  exact ⟨D,hm,hr,ho,sz.trans budget,all⟩

private noncomputable def signature (f : F n) : Bool × Bool × Finset (I n) × Finset (I n) :=
  (f (fun _ => false), f (fun _ => true),
   Finset.univ.filter (fun j => f (fun i => decide (i=j)) ≠ f (fun _ => false)),
   Finset.univ.filter (fun j => f (fun i => decide (i≠j)) ≠ f (fun _ => true)))

private theorem sigConst (b : Bool) : signature (n:=n) (fun _ => b) = (b,b,∅,∅) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    simp [signature]
  · ext j
    simp [signature]

private theorem sigPos (i : I n) : signature (n:=n) (pos i) = (false,true,{i},{i}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases h : i=j <;> simp_all [signature,pos] <;> grind
  · ext j
    by_cases h : i=j <;> simp_all [signature,pos] <;> grind

private theorem sigNeg (i : I n) : signature (n:=n) (neg i) = (true,false,{i},{i}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases h : i=j <;> simp_all [signature,neg] <;> grind
  · ext j
    by_cases h : i=j <;> simp_all [signature,neg] <;> grind

private theorem sigSame (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (eqBit e) = (true,true,{e.1,e.2},{e.1,e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,eqBit] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,eqBit] <;> grind

private theorem sigDiff (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (xorBit e) = (false,false,{e.1,e.2},{e.1,e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,xorBit] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,xorBit] <;> grind

private theorem sigZero (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (zz e) = (true,false,{e.1,e.2},∅) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zz] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zz] <;> grind

private theorem sigLeft (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (oz e) = (false,false,{e.1},{e.2}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,oz] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,oz] <;> grind

private theorem sigRight (e : Edge n) (h : e.1≠e.2) : signature (n:=n) (zo e) = (false,false,{e.2},{e.1}) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zo] <;> grind
  · ext j
    by_cases a : e.1=j <;> by_cases b : e.2=j <;> simp_all [signature,zo] <;> grind

private noncomputable def tag (f : F n) : Nat :=
  let z := signature f
  if z.1 then (if z.2.1 then 0 else if z.2.2.2.Nonempty then 1 else 2)
  else if z.2.1 then 0 else if z.2.2.1.card=1 then 3 else 0

private theorem negInj : Function.Injective (neg (n:=n)) := by
  intro i j same
  have h := congrArg signature same
  simpa [sigNeg] using h

theorem countTargets (E : Finset (Edge n)) (sorted : ∀ e∈E, e.1<e.2) (S : Finset (I n)) :
    ((target E) \ (raw E ∪ S.image neg)).card = n + 3*E.card - S.card := by
  classical
  have ne (e) (he : e∈E) := ne_of_lt (sorted e he)
  have zeroTag (e) (he : e∈E) : tag (zz e)=2 := by simp [tag,sigZero e (ne e he)]
  have leftTag (e) (he : e∈E) : tag (oz e)=3 := by simp [tag,sigLeft e (ne e he)]
  have rightTag (e) (he : e∈E) : tag (zo e)=3 := by simp [tag,sigRight e (ne e he)]
  have negTag (i : I n) : tag (neg i)=1 := by simp [tag,sigNeg]
  have rawTag (f) (hf : f∈raw E) : tag f=0 := by
    simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,
      Finset.mem_univ,true_and] at hf
    rcases hf with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
    · simp [tag,sigConst]
    · simp [tag,sigConst]
    · simp [tag,sigPos]
    · simp [tag,sigSame e (ne e he)]
    · simp [tag,sigDiff e (ne e he),ne e he]
  have zeroInj : Set.InjOn zz (E : Set (Edge n)) := by
    intro e he d hd eq
    have hs := congrArg (fun z => (signature z).2.2.1) eq
    simp only [sigZero e (ne e he),sigZero d (ne d hd)] at hs
    have ha : e.1∈({d.1,d.2}:Finset (I n)) := hs ▸ Finset.mem_insert_self _ _
    have hb : e.2∈({d.1,d.2}:Finset (I n)) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    have ea := sorted e he
    have eb := sorted d hd
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.ext_iff] at ha hb <;> change e.1.val < e.2.val at ea <;> change d.1.val < d.2.val at eb <;> omega
  have leftInj : Set.InjOn oz (E : Set (Edge n)) := by
    intro e he d hd eq
    have h := congrArg signature eq
    simp [sigLeft e (ne e he),sigLeft d (ne d hd)] at h
    exact Prod.ext h.1 h.2
  have rightInj : Set.InjOn zo (E : Set (Edge n)) := by
    intro e he d hd eq
    have h := congrArg signature eq
    simp [sigRight e (ne e he),sigRight d (ne d hd)] at h
    exact Prod.ext h.2 h.1
  let V := Finset.univ.image (neg (n:=n))
  let Z := E.image zz
  let A := E.image oz
  let B := E.image zo
  have vTag f (hf : f∈V) : tag f=1 := by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf; exact negTag i
  have zTag f (hf : f∈Z) : tag f=2 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact zeroTag e he
  have aTag f (hf : f∈A) : tag f=3 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact leftTag e he
  have bTag f (hf : f∈B) : tag f=3 := by obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf; exact rightTag e he
  have diffAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro f ha hb
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hb
    have h := congrArg signature eq
    simp [sigLeft e (ne e he),sigRight d (ne d hd)] at h
    have ea := sorted e he
    have da := sorted d hd
    obtain ⟨ha,hb⟩ := h
    rw [←ha,←hb] at ea
    exact (lt_asymm ea da)
  have dvz : Disjoint V Z := Finset.disjoint_left.mpr (fun {f} h k => by have := vTag f h; have := zTag f k; omega)
  have dva : Disjoint (V∪Z) A := by
    apply Finset.disjoint_left.mpr
    intro f hx hy
    have := aTag _ hy
    rcases Finset.mem_union.mp hx with h|h
    · have := vTag _ h; omega
    · have := zTag _ h; omega
  have dvb : Disjoint (V∪Z∪A) B := by
    apply Finset.disjoint_left.mpr
    intro f hx hy
    have := bTag _ hy
    rcases Finset.mem_union.mp hx with h|h
    · rcases Finset.mem_union.mp h with h|h
      · have := vTag _ h; omega
      · have := zTag _ h; omega
    · exact Finset.disjoint_left.mp diffAB h hy
  have ct : (target E).card=n+3*E.card := by
    change (V∪Z∪A∪B).card=_
    rw [Finset.card_union_of_disjoint dvb,Finset.card_union_of_disjoint dva,Finset.card_union_of_disjoint dvz]
    simp only [V,Z,A,B,Finset.card_image_of_injective _ negInj,Finset.card_image_of_injOn zeroInj,
      Finset.card_image_of_injOn leftInj,Finset.card_image_of_injOn rightInj,Finset.card_univ,Fintype.card_fin]
    omega
  have disj : Disjoint (target E) (raw E) := by
    apply Finset.disjoint_left.mpr
    intro f ht hr
    have h0 := rawTag _ hr
    change f∈V∪Z∪A∪B at ht
    simp only [Finset.mem_union] at ht
    rcases ht with (((h|h)|h)|h)
    · have := vTag _ h; omega
    · have := zTag _ h; omega
    · have := aTag _ h; omega
    · have := bTag _ h; omega
  have sub : S.image neg ⊆ target E := by
    rintro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    simp [target]
  have drop : target E \ (raw E ∪ S.image neg) = target E \ S.image neg := by
    ext f
    simp only [Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun h => ⟨h.1,fun v => h.2 (Or.inr v)⟩,fun h => ⟨h.1,fun v => v.elim
      (Finset.disjoint_left.mp disj h.1) h.2⟩⟩
  rw [drop,Finset.card_sdiff_of_subset sub,ct,Finset.card_image_of_injective _ negInj]

set_option maxHeartbeats 1000000 in
theorem criterion :
∀ (n : Nat) (E : Finset (Fin n × Fin n)), (∀ e ∈ E, e.1 < e.2) →
  ∀ (S : Finset (Fin n)),
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let F := (Fin n → Bool) → Bool
  let bit := fun (i : Fin n) (x : Fin n → Bool) => x i
  let inv := fun (i : Fin n) (x : Fin n → Bool) => !(x i)
  let eqBit := fun (e : Fin n × Fin n) (x : Fin n → Bool) => x e.1 == x e.2
  let diff := fun (e : Fin n × Fin n) (x : Fin n → Bool) => xor (x e.1) (x e.2)
  let raw : Finset F := {fun _ => false, fun _ => true} ∪ Finset.univ.image bit ∪ E.image eqBit ∪ E.image diff
  let starts := raw ∪ S.image inv
  let demand : Finset F := Finset.univ.image inv ∪
    E.image (fun e x => !(x e.1) && !(x e.2)) ∪ E.image (fun e x => x e.1 && !(x e.2)) ∪
    E.image (fun e x => !(x e.1) && x e.2)
  let hit := ∀ C : Finset (Fin n), C.Nonempty → (∀ e∈E, e.1∈C ↔ e.2∈C) → ∃ i∈C, i∈S
  (demand \ starts).card = n+3*E.card-S.card ∧
  ∀ (L : List F), L.toFinset = starts → ∀ p : Nat,
    (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length D ∧
      D.output < L.length+D.size ∧ D.size ≤ p ∧
      ∀ f∈demand, ∃ i<L.length+D.size, ∀ x, (D.wires (L.map (fun z => z x))).getD i false = f x) ↔
    hit ∧ n+3*E.card-S.card ≤ p
:= by
  intro n E sorted S
  dsimp only
  have count := countTargets E sorted S
  dsimp only [target,raw,pos,neg,eqBit,xorBit,zz,oz,zo] at count
  constructor
  · convert! count using 0 <;> congr! <;> apply Subsingleton.elim
  intro L h p
  have inputs : L.toFinset = raw E ∪ S.image neg := by
    dsimp only [raw,pos,neg,eqBit,xorBit]
    convert! h using 0 <;> congr! <;> apply Subsingleton.elim
  have bound := exactBudget E S L inputs p
  rw [inputs,countTargets E sorted S] at bound
  dsimp only [fits,sampleFits,target,neg,zz,oz,zo,row,sampleRow,hits] at bound
  convert! bound using 0 <;> congr! <;> apply Subsingleton.elim

end PEqualNP.Outside.L_lib_1457.Core.GraphInversionSeeds

namespace PEqualNP.Outside.L_lib_1457.Core.GraphSeedSamples

open Classical CircuitLowerBounds MetaComplexity FiniteGateBank

abbrev Word (n : Nat) := Finset (Fin n)
abbrev Test (n : Nat) := Word n → Bool

def row (L : List (Test n)) (x : Word n) := L.map (fun f => f x)
def ordered (L : List (Test n)) (x y : Word n) := ∀ f∈L, f x=true → f y=true

def fits (A : Finset (Word n)) (L : List (Test n)) (T : Finset (Test n)) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧ C.output<L.length+C.size ∧
    ∀ f∈T, ∃ j<L.length+C.size, ∀ x∈A, (C.wires (row L x)).getD j false=f x

private theorem everyList {X J : Type} {w : Nat} {r : X → List Bool}
    (width : ∀ x,(r x).length=w) (p : Net w) (one : p.has r (fun _ => true))
    (l : List J) (f : J → X → Bool) (live : ∀ i∈l,p.has r (f i)) :
    ∃ q, Grow r p q l.length 0 ∧ q.has r (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,one⟩
  | cons i l ih =>
    obtain ⟨q,g,old⟩ := ih (fun j hj => live j (by simp [hj]))
    obtain ⟨s,k,out⟩ := binary width q _ _ (g.1 _ (live i (by simp))) old true
    exact ⟨s,chain g k,by simpa [List.all_cons] using out⟩

private theorem interpolation (A : Finset (Word n)) (L : List (Test n)) (T : Finset (Test n))
    (zero : (fun _ => false)∈L) (one : (fun _ => true)∈L) :
    fits A L T ↔ ∀ x∈A, ∀ y∈A, ordered L x y → ∀ f∈T, f x=true → f y=true := by
  constructor
  · rintro ⟨C,mono,_,_,get⟩ x hx y hy ord f hf fv
    obtain ⟨j,_,val⟩ := get f hf
    have le : LowMergeProof.LeL (row L x) (row L y) := by
      intro i
      by_cases h : i<L.length
      · rw [List.getD_eq_getElem _ _ (by simpa [row] using h : i<(row L x).length),
          List.getD_eq_getElem _ _ (by simpa [row] using h : i<(row L y).length)]
        simpa [row] using ord L[i] (List.getElem_mem h)
      · simp [row,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]
    have imp := LowMergeProof.wires_mono C (fun g hg => (mono g hg).1) _ _ (by simp [row]) le j
    rw [val x hx,val y hy] at imp
    exact imp fv
  · intro mono
    let r := fun x : A => row L x.val
    have width (x : A) : (r x).length=L.length := by simp [r,row]
    let p := empty L.length
    have inp (f : Test n) (hf : f∈L) : p.has r (fun x => f x.val) := by
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hf
      refine ⟨i,by simpa [p,empty] using hi,?_⟩
      intro x
      change (row L x.val).getD i false = f x.val
      rw [List.getD_eq_getElem _ _ (by simpa [row] using hi)]
      simpa [row] using congrFun he x.val
    let U := A.toList
    let term := fun (x : Word n) (y : A) => (L.filter (fun f => f x)).all (fun f => f y.val)
    have termIff (x : Word n) (y : A) : term x y=true ↔ ordered L x y := by
      simp only [term,ordered,List.all_eq_true,List.mem_filter,and_imp]
    obtain ⟨q,cq,allTerms⟩ := batch (raw:=r) p U term L.length 0 (by
      intro x _ net keep
      obtain ⟨s,gs,out⟩ := everyList width net (keep _ (inp _ one)) (L.filter (fun f => f x))
        (fun f y => f y.val) (fun f hf => keep _ (inp f (List.mem_filter.mp hf).1))
      exact ⟨s,allowance gs (List.length_filter_le ..),out⟩)
    obtain ⟨s,cs,allOut⟩ := batch (raw:=r) q T.toList (fun f (x : A) => f x.val) U.length 0 (by
      intro f hf net keep
      obtain ⟨v,gv,out⟩ := anyList width net (keep _ (cq.1 _ (inp _ zero))) (U.filter f) term
        (fun x hx => keep _ (allTerms x (List.mem_filter.mp hx).1))
      refine ⟨v,allowance gv (List.length_filter_le ..),?_⟩
      have eq : (fun y : A => (U.filter f).any (fun x => term x y)) = fun y => f y.val := by
        funext y
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true]
        constructor
        · rintro ⟨x,hx,holds⟩
          obtain ⟨a,b⟩ := List.mem_filter.mp hx
          exact mono x (by simpa [U] using a) y.val y.property ((termIff x y).mp holds) f
            (by simpa using hf) b
        · intro b
          exact ⟨y.val,List.mem_filter.mpr ⟨by simpa [U] using y.property,b⟩,
            (termIff _ _).mpr (fun _ _ => id)⟩
      exact eq ▸ out)
    let C : Circuit := ⟨s.gates,0⟩
    have cost : s.cost=0 := by rw [cs.2.2,cq.2.2]; simp [p,empty,Net.cost,NotBracket.notCount]
    have no : (C.gates.filter (fun g => decide (g.op=GateOp.not)))=[] := by
      apply List.length_eq_zero_iff.mp
      simpa [C,Net.cost,NotBracket.notCount] using cost
    refine ⟨C,?_,s.readsBack,by have := List.length_pos_of_mem zero; change 0<L.length+_; omega,?_⟩
    · intro g hg
      have ops := s.fan g hg
      have notGate : g.op≠GateOp.not := by
        intro h
        have m : g∈C.gates.filter (fun t => decide (t.op=GateOp.not)) := by simp [hg,h]
        rw [no] at m
        simp at m
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff,notGate] using ops
    · intro f hf
      obtain ⟨j,hj,h⟩ := allOut f (by simpa using hf)
      exact ⟨j,hj,fun x hx => h ⟨x,hx⟩⟩

abbrev Edge (n : Nat) := Fin n × Fin n
def bit (i : Fin n) (x : Word n) := decide (i∈x)
def inv (i : Fin n) (x : Word n) := decide (i∉x)
def same (e : Edge n) (x : Word n) := decide (e.1∈x ↔ e.2∈x)
def cross (e : Edge n) (x : Word n) := !(same e x)

noncomputable def bank (E : Finset (Edge n)) (S : Word n) : Finset (Test n) :=
  {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪ E.image same ∪ E.image cross ∪ S.image inv

def closed (E : Finset (Edge n)) (V : Word n) := ∀ e∈E, e.1∈V ↔ e.2∈V

private theorem orderIff (E : Finset (Edge n)) (S x y : Word n) :
    ordered (bank E S).toList x y ↔ x⊆y ∧ closed E (y\x) ∧ Disjoint (y\x) S := by
  classical
  constructor
  · intro ord
    have raw (f) (hf : f∈bank E S) := ord f (by simpa using hf)
    have sub : x⊆y := by
      intro i hi
      exact of_decide_eq_true (raw (bit i) (by simp [bank]) (by simpa [bit] using hi))
    refine ⟨sub,?_,?_⟩
    · intro e he
      have a := raw (same e) (by simp only [bank,Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ he))))
      have b := raw (cross e) (by simp only [bank,Finset.mem_union]; exact Or.inl (Or.inr (Finset.mem_image_of_mem _ he)))
      have s := @sub e.1
      have t := @sub e.2
      simp [same,cross] at a b
      simp only [Finset.mem_sdiff]
      tauto
    · apply Finset.disjoint_left.mpr
      intro i hi hs
      have a := raw (inv i) (by simp only [bank,Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hs))
      have p := Finset.mem_sdiff.mp hi
      simpa [inv,p.1,p.2] using a
  · rintro ⟨sub,c,d⟩ f hf
    have h : f∈bank E S := by simpa using hf
    simp only [bank,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,
      Finset.mem_univ,true_and] at h
    rcases h with (((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨i,hi,rfl⟩)
    · exact id
    · exact id
    · simpa [bit] using @sub i
    · have a := c e he
      have s := @sub e.1
      have t := @sub e.2
      simp only [Finset.mem_sdiff] at a
      simp [same]
      tauto
    · have a := c e he
      have s := @sub e.1
      have t := @sub e.2
      simp only [Finset.mem_sdiff] at a
      simp [cross,same]
      tauto
    · simp [inv]
      intro hx hy
      exact Finset.disjoint_left.mp d (Finset.mem_sdiff.mpr ⟨hy,hx⟩) hi

def detects (A : Finset (Word n)) (E : Finset (Edge n)) (S : Word n) :=
  ∀ x∈A, ∀ y∈A, x⊆y → closed E (y\x) → Disjoint (y\x) S → y=x

private theorem fitIff (A : Finset (Word n)) (E : Finset (Edge n)) (S : Word n)
    (T : Finset (Test n)) (required : ∀ i, inv i∈T) :
    fits A (bank E S).toList T ↔ detects A E S := by
  rw [interpolation A _ T (by simp [bank]) (by simp [bank])]
  constructor
  · intro can x hx y hy sub c d
    have ord := (orderIff E S x y).mpr ⟨sub,c,d⟩
    apply Finset.Subset.antisymm _ sub
    intro i hi
    by_contra h
    have v := can x hx y hy ord (inv i) (required i) (by simp [inv,h])
    simpa [inv,hi] using v
  · intro det x hx y hy ord f _ fx
    obtain ⟨sub,c,d⟩ := (orderIff E S x y).mp ord
    rw [det x hx y hy sub c d]
    exact fx

private theorem edgesBound {I : Type} [DecidableEq I] (D : Finset I) (A : Finset (Finset I))
    (nonempty : A.Nonempty)
    (edges : ∀ j∈D, ∃ x∈A, j∉x ∧ insert j x∈A) : D.card+1≤A.card := by
  classical
  induction D using Finset.induction_on generalizing A with
  | empty => simpa using Finset.card_pos.mpr nonempty
  | @insert j D hj ih =>
    let erase := fun u : Finset I => u.erase j
    obtain ⟨w,hw,miss,hw'⟩ := edges j (Finset.mem_insert_self ..)
    have collide : erase w=erase (insert j w) := by simp [erase,miss]
    have smaller : (A.image erase).card < A.card := by
      apply lt_of_le_of_ne Finset.card_image_le
      intro eq
      have k := (Finset.card_image_iff.mp eq) hw hw' collide
      exact miss (k.symm ▸ Finset.mem_insert_self ..)
    have bound := ih (A.image erase) (nonempty.image _) (by
      intro i hi
      have neq : i≠j := fun h => hj (h ▸ hi)
      obtain ⟨x,hx,absent,mem⟩ := edges i (Finset.mem_insert_of_mem hi)
      refine ⟨erase x,Finset.mem_image_of_mem _ hx,by simp [erase,absent],?_⟩
      have eq : erase (insert i x)=insert i (erase x) := by ext z; simp [erase]; grind
      exact eq ▸ Finset.mem_image_of_mem _ mem)
    rw [Finset.card_insert_of_notMem hj]
    omega

noncomputable def block (color : Fin n → Fin c) (j : Fin c) : Word n :=
  Finset.univ.filter (fun i => color i=j)
def cover (color : Fin n → Fin c) (S : Word n) := ∀ j, ∃ i∈S, color i=j
def tested (A : Finset (Word n)) (color : Fin n → Fin c) :=
  ∀ j, ∃ x∈A, Disjoint x (block color j) ∧ x∪block color j∈A

def preserves (A : Finset (Word n)) (E : Finset (Edge n)) (color : Fin n → Fin c)
    (T : Finset (Test n)) :=
  ∀ S, fits A (bank E S).toList T ↔ cover color S

private theorem sampleIff (color : Fin n → Fin c) (onto : Function.Surjective color)
    (E : Finset (Edge n))
    (classes : ∀ V, closed E V ↔ ∀ i k, color i=color k → (i∈V ↔ k∈V))
    (T : Finset (Test n)) (required : ∀ i, inv i∈T) (A : Finset (Word n)) :
    preserves A E color T ↔ tested A color := by
  constructor
  · intro keeps j
    let B := block color j
    let S := Finset.univ\B
    have missed : ¬cover color S := by
      intro cov
      obtain ⟨i,hi,e⟩ := cov j
      simpa [S,B,block,e] using hi
    have fail := fun h => missed ((keeps S).mp ((fitIff A E S T required).mpr h))
    change ¬detects A E S at fail
    unfold detects at fail
    push_neg at fail
    obtain ⟨x,hx,y,hy,sub,cl,d,ne⟩ := fail
    obtain ⟨i,hi⟩ : (y\x).Nonempty := by
      by_contra! h
      exact ne (Finset.Subset.antisymm (fun k hk => by
        by_contra missing
        have m := Finset.mem_sdiff.mpr ⟨hk,missing⟩
        rw [h] at m
        exact Finset.notMem_empty _ m) sub)
    have inside (k) (hk : k∈y\x) : color k=j := by
      by_contra neq
      exact Finset.disjoint_left.mp d hk (by simp [S,B,block,neq])
    have diff : y\x=B := by
      ext k
      constructor
      · intro hk
        simpa [B,block] using inside k hk
      · intro hk
        have eq : color k=j := by simpa [B,block] using hk
        exact ((classes _).mp cl i k ((inside i hi).trans eq.symm)).mp hi
    refine ⟨x,hx,?_,?_⟩
    · change Disjoint x B
      rw [←diff]
      exact Finset.disjoint_sdiff
    · have together : x∪B=y := by rw [←diff]; ext k; simp; grind
      change x∪B∈A
      rwa [together]
  · intro supports S
    rw [fitIff A E S T required]
    constructor
    · intro det j
      by_contra! absent
      obtain ⟨x,hx,d,hi⟩ := supports j
      let B := block color j
      have diff : (x∪B)\x=B := by
        ext v
        have guard : v∈x → v∈B → False := fun h k => Finset.disjoint_left.mp d h k
        simp only [Finset.mem_sdiff,Finset.mem_union]
        change (v∈x ∨ v∈B) ∧ v∉x ↔ v∈B
        grind
      have cl : closed E B := (classes _).mpr (by intro i k eq; simp [B,block,eq])
      have miss : Disjoint B S := Finset.disjoint_left.mpr (by
        intro i he hs
        exact absent i hs (by simpa [B,block] using he))
      have eq := det x hx (x∪B) hi Finset.subset_union_left (by rwa [diff]) (by rwa [diff])
      obtain ⟨i,eqi⟩ := onto j
      have bi : i∈B := by simp [B,block,eqi]
      have inside : i∈x∪B := Finset.mem_union_right _ bi
      exact Finset.disjoint_left.mp d (eq ▸ inside) bi
    · intro hit x _ y _ sub cl dis
      apply Finset.Subset.antisymm _ sub
      intro i hi
      by_contra missing
      have mem : i∈y\x := Finset.mem_sdiff.mpr ⟨hi,missing⟩
      obtain ⟨k,hk,eq⟩ := hit (color i)
      exact Finset.disjoint_left.mp dis (((classes _).mp cl i k eq.symm).mp mem) hk

private theorem leastSample (color : Fin n → Fin c) (onto : Function.Surjective color)
    (A : Finset (Word n)) (full : tested A color) (pos : 0<c) : c+1≤A.card := by
  classical
  choose representative rep using onto
  let project := fun x : Word n => Finset.univ.filter (fun j : Fin c => representative j∈x)
  let P := A.image project
  obtain ⟨w,hw,_,_⟩ := full (⟨0,pos⟩ : Fin c)
  have bound := edgesBound (Finset.univ : Finset (Fin c)) P ⟨_,Finset.mem_image_of_mem _ hw⟩ (by
    intro j _
    obtain ⟨x,hx,d,both⟩ := full j
    have reprB : representative j∈block color j := by simp [block,rep]
    have out : representative j∉x := fun h => Finset.disjoint_left.mp d h reprB
    refine ⟨project x,Finset.mem_image_of_mem _ hx,by simp [project,out],?_⟩
    have eq : project (x∪block color j)=insert j (project x) := by
      ext k
      simp [project,block,rep,or_comm]
    exact eq ▸ Finset.mem_image_of_mem _ both)
  exact (by simpa using bound : c+1≤P.card).trans Finset.card_image_le

private theorem star (color : Fin n → Fin c) :
    ∃ A : Finset (Word n), A.card≤c+1 ∧ tested A color := by
  classical
  let A := insert ∅ (Finset.univ.image (block color))
  refine ⟨A,?_,?_⟩
  · have h := Finset.card_insert_le (∅ : Word n) (Finset.univ.image (block color))
    have b : (Finset.univ.image (block color)).card≤c := Finset.card_image_le.trans (by simp)
    exact h.trans (by omega)
  · intro j
    exact ⟨∅,by simp [A],by simp,by simp [A]⟩

theorem criterion :
∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  Function.Surjective color →
  (∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
    ∀ i j, color i=color j → (i∈V ↔ j∈V)) →
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i∈x)
  let inv := fun (i : Fin n) (x : W) => decide (i∉x)
  let same := fun (e : Fin n × Fin n) (x : W) => decide (e.1∈x ↔ e.2∈x)
  let bank := fun S : W => (({fun _ : W => false,fun _ : W => true} : Finset (W → Bool)) ∪
    Finset.univ.image bit ∪ E.image same ∪ E.image (fun e x => !(same e x)) ∪ S.image inv).toList
  let B := fun j : Fin c => Finset.univ.filter (fun i => color i=j)
  ∀ T : Finset (W → Bool), (∀ i, inv i∈T) →
    let keeps := fun A : Finset W => ∀ S : W,
      (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (bank S).length D ∧
        D.output < (bank S).length+D.size ∧ ∀ f∈T, ∃ j<(bank S).length+D.size,
          ∀ x∈A, (D.wires ((bank S).map (fun g => g x))).getD j false=f x) ↔
      ∀ j, ∃ i∈S, color i=j
    (∀ A, keeps A ↔ ∀ j, ∃ x∈A, Disjoint x (B j) ∧ x∪B j∈A) ∧
    (∃ A, keeps A ∧ A.card=(if c=0 then 0 else c+1) ∧ ∀ A', keeps A' → A.card≤A'.card)
:= by
  classical
  intro n c E color onto classes
  dsimp only
  intro T req
  change (∀ A, preserves A E color T ↔ tested A color) ∧
    ∃ A, preserves A E color T ∧ A.card=(if c=0 then 0 else c+1) ∧
      ∀ A', preserves A' E color T → A.card≤A'.card
  have iff := sampleIff color onto E classes T req
  refine ⟨iff,?_⟩
  by_cases h : c=0
  · subst c
    exact ⟨∅,(iff _).mpr (fun j => Fin.elim0 j),by simp,by simp⟩
  · have pos : 0<c := Nat.pos_of_ne_zero h
    obtain ⟨A,sz,ok⟩ := star color
    have lo := leastSample color onto A ok pos
    exact ⟨A,(iff _).mpr ok,by simp [h]; omega,
      fun A' hA => sz.trans (leastSample color onto _ ((iff _).mp hA) pos)⟩

end PEqualNP.Outside.L_lib_1457.Core.GraphSeedSamples

namespace PEqualNP.Outside.L_lib_1457.Core.GraphPriceCalibration

noncomputable section

open Classical GraphInversionSeeds CircuitLowerBounds MetaComplexity

abbrev Rows (m n : Nat) := Fin m → Fin n → Bool
abbrev Trace (m : Nat) := Fin m → Bool
abbrev proj (x : Rows m n) (f : F n) : Trace m := fun k => f (x k)
abbrev R (x : Rows m n) (E : Finset (Edge n)) := (raw E).image (proj x)
abbrev T (x : Rows m n) (E : Finset (Edge n)) := (target E).image (proj x)
abbrev N (x : Rows m n) (S : Finset (Fin n)) := S.image fun i => proj x (neg i)
abbrev bank (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n)) := R x E ∪ N x S
abbrev price (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n)) :=
  ((T x E) \ bank x E S).card
def serves (color : Fin n → Fin c) (S : Finset (Fin n)) := ∀ j, ∃ i∈S, color i=j
def classes (E : Finset (Edge n)) (color : Fin n → Fin c) := ∀ V : Finset (Fin n),
  (∀ e∈E, e.1∈V ↔ e.2∈V) ↔ ∀ i k, color i=color k → (i∈V ↔ k∈V)
def pure (x : Rows m n) (color : Fin n → Fin c) := ∀ j, ∃ a b,
  (∀ i, color i=j → x a i=false ∧ x b i=true) ∧ (∀ i, color i≠j → x a i=x b i)

private theorem reach (part : classes E color) (h : serves color S) : hits E S := by
  intro V hv closed
  obtain ⟨i,hi⟩ := hv
  obtain ⟨k,hk,eq⟩ := h (color i)
  exact ⟨k,((part _).mp closed i k eq.symm).mp hi,hk⟩

private theorem build (x : Rows m n) (E : Finset (Edge n)) (S : Finset (Fin n))
    (L : List (Trace m)) (inputs : L.toFinset=bank x E S) (h : hits E S) :
    sampleFits L (T x E) (price x E S) := by
  classical
  have occupied : (bank x E S).Nonempty := ⟨_,Finset.mem_union_left _
    (Finset.mem_image_of_mem (proj x) (show (fun _ => false)∈raw E by simp [raw]))⟩
  have len : 0<L.length := by
    rw [←inputs] at occupied
    obtain ⟨f,hf⟩ := occupied
    exact List.length_pos_of_mem (List.mem_toFinset.mp hf)
  apply (by simpa only [inputs] using tightBuild L (T x E) len)
  intro U known stable
  let V := (raw E ∪ target E).filter (fun f => proj x f∈U)
  have base : raw E ⊆ V := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf,
      known (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf))⟩
  have seeds : ∀ i∈S, neg i∈V := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (by simp [target]),
      known (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))⟩
  have doneT := grow E S (target E) V h base (by rfl) seeds (by
    rintro f hf ⟨a,ha,b,hb,op⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hf,
      stable _ (Finset.mem_image_of_mem _ hf) ⟨proj x a,(Finset.mem_filter.mp ha).2,
        proj x b,(Finset.mem_filter.mp hb).2,?_⟩⟩
    rcases op with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl)
  intro g hg
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
  exact (Finset.mem_filter.mp (doneT hf)).2

private theorem pureOrder (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (j : Fin c) {a b : Fin m}
    (flips : ∀ i, color i=j → x a i=false ∧ x b i=true)
    (fixed : ∀ i, color i≠j → x a i=x b i) :
    ∀ f∈R x E, f a=true → f b=true := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  have edge (e) (he : e∈E) : color e.1=color e.2 := by
    let V := Finset.univ.filter (fun i => color i=color e.2)
    have closed := (part V).mpr (by intro i k eq; simp [V,eq])
    simpa [V] using (closed e he).mpr (by simp [V])
  simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_image,Finset.mem_univ,true_and] at hg
  rcases hg with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
  · exact id
  · exact id
  · by_cases h : color i=j
    · simp [proj,pos,(flips i h).1]
    · simp [proj,pos,fixed i h]
  · by_cases h : color e.2=j
    · have k := (edge e he).trans h
      simp [proj,eqBit,(flips e.1 k).1,(flips e.1 k).2,(flips e.2 h).1,(flips e.2 h).2]
    · have k : color e.1≠j := by simpa [edge e he] using h
      simp [proj,eqBit,fixed e.1 k,fixed e.2 h]
  · by_cases h : color e.2=j
    · have k := (edge e he).trans h
      simp [proj,xorBit,(flips e.1 k).1,(flips e.2 h).1]
    · have k : color e.1≠j := by simpa [edge e he] using h
      simp [proj,xorBit,fixed e.1 k,fixed e.2 h]

private theorem physical (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (onto : Function.Surjective color) (part : classes E color) (w : pure x color)
    (S : Finset (Fin n)) (L : List (Trace m)) (inputs : L.toFinset=bank x E S) (p : Nat) :
    sampleFits L (T x E) p ↔ serves color S ∧ price x E S≤p := by
  constructor
  · intro fit
    refine ⟨?_,by simpa only [inputs] using countMissing L (T x E) fit⟩
    intro j
    by_contra! missed
    obtain ⟨a,b,flip,fixed⟩ := w j
    have rawOrd := pureOrder x color E part j flip fixed
    obtain ⟨C,mono,_,_,_,all⟩ := fit
    have ord : LowMergeProof.LeL (sampleRow L a) (sampleRow L b) := by
      intro k
      by_cases hk : k<L.length
      · rw [List.getD_eq_getElem _ _ (by simpa [sampleRow] using hk : k<(sampleRow L a).length),
            List.getD_eq_getElem _ _ (by simpa [sampleRow] using hk : k<(sampleRow L b).length)]
        simp only [sampleRow,List.getElem_map]
        have mem : L[k]∈bank x E S := inputs ▸ List.mem_toFinset.mpr (List.getElem_mem hk)
        rcases Finset.mem_union.mp mem with hr|hs
        · exact rawOrd _ hr
        · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hs
          rw [←eq]; simp [proj,neg,fixed i (missed i hi)]
      · simp [sampleRow,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hk)]
    obtain ⟨i,hi⟩ := onto j
    obtain ⟨k,_,read⟩ := all (proj x (neg i)) (Finset.mem_image_of_mem _ (by simp [target]))
    have imp := LowMergeProof.wires_mono C (fun g hg => (mono g hg).1) _ _
      (by simp [sampleRow]) ord k
    rw [read a,read b] at imp
    simp [proj,neg,(flip i hi).1,(flip i hi).2] at imp
  · rintro ⟨cover,le⟩
    obtain ⟨C,hm,hr,ho,sz,hf⟩ := build x E S L inputs (reach part cover)
    exact ⟨C,hm,hr,ho,sz.trans le,hf⟩

private theorem ordinary (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (w : pure x color) (i : Fin n) : proj x (neg i)∉R x E := by
  intro rawMem
  obtain ⟨a,b,flip,fixed⟩ := w (color i)
  have imp := pureOrder x color E part (color i) flip fixed _ rawMem
  simp [proj,neg,(flip i rfl).1,(flip i rfl).2] at imp

private theorem traceSum (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (part : classes E color) (w : pure x color) (S : Finset (Fin n)) :
    price x E S + (N x S).card = ((T x E)\R x E).card := by
  let P := (T x E)\R x E
  have sub : N x S ⊆ P := by
    rintro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (by simp [target]),ordinary x color E part w i⟩
  have eq : ((T x E)\bank x E S) = P\N x S := by
    ext f
    simp only [P,bank,Finset.mem_sdiff,Finset.mem_union]; tauto
  unfold price
  rw [eq,Finset.card_sdiff_of_subset sub]
  exact Nat.sub_add_cancel (Finset.card_le_card sub)

private theorem seedCard (x : Rows m n) (color : Fin n → Fin c) (w : pure x color)
    (K : Finset (Fin n)) (inj : Set.InjOn color K) : (N x K).card=K.card := by
  apply Finset.card_image_of_injOn
  intro i hi k hk eq
  apply inj hi hk
  by_contra ne
  obtain ⟨a,b,flip,fixed⟩ := w (color i)
  have v := fixed k (Ne.symm ne)
  have aeq := congrFun eq a
  have beq := congrFun eq b
  simp only [proj,neg,(flip i rfl).1,(flip i rfl).2,Bool.not_false,Bool.not_true,v] at aeq beq
  grind

private theorem fullBound (x : Rows m n) (E : Finset (Edge n)) (sorted : ∀ e∈E,e.1<e.2)
    (S : Finset (Fin n)) : price x E S≤n+3*E.card-S.card := by
  let full := target E \ (raw E ∪ S.image neg)
  have inc : T x E \ bank x E S ⊆ full.image (proj x) := by
    intro f hf
    obtain ⟨ht,absent⟩ := Finset.mem_sdiff.mp hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_image_of_mem
    refine Finset.mem_sdiff.mpr ⟨hg,?_⟩
    intro present
    apply absent
    rcases Finset.mem_union.mp present with hr|hs
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
  exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans
    (le_of_eq (countTargets E sorted S)))

private theorem calibrate (x : Rows m n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (sorted : ∀ e∈E,e.1<e.2) (part : classes E color) (w : pure x color)
    (K : Finset (Fin n)) (one : ∀ j, ∃! i, i∈K ∧ color i=j)
    (L : Finset (Fin n) → List (Trace m)) (inputs : ∀ S, (L S).toFinset=bank x E S) :
    (∀ S p, sampleFits (L S) (T x E) p ↔ serves color S ∧ price x E S≤p) ∧
    (∀ S, price x E S+(N x S).card=price x E K+K.card) ∧
    ((∀ p, sampleFits (L K) (T x E) p ↔ n+3*E.card-K.card≤p) ↔
     ∀ S p, sampleFits (L S) (T x E) p ↔ serves color S ∧ n+3*E.card-S.card≤p) := by
  have cov : serves color K := fun j => by
    obtain ⟨i,hi,_⟩ := one j
    exact ⟨i,hi⟩
  have onto : Function.Surjective color := fun j => by
    obtain ⟨i,_,eq⟩ := cov j
    exact ⟨i,eq⟩
  have inj : Set.InjOn color K := by
    intro i hi k hk eq
    exact (one (color k)).unique ⟨hi,eq⟩ ⟨hk,rfl⟩
  have phys := fun S => physical x color E onto part w S (L S) (inputs S)
  have identity (S) : price x E S+(N x S).card=price x E K+K.card := by
    rw [←seedCard x color w K inj,traceSum x color E part w,traceSum x color E part w]
  refine ⟨phys,identity,?_⟩
  constructor
  · intro anchor S p
    have lb := (anchor (price x E K)).mp ((phys K _).mpr ⟨cov,le_rfl⟩)
    have kb : K.card≤n := Finset.card_le_univ K |>.trans (by simp)
    have ub := fullBound x E sorted S
    have cnt : (N x S).card≤S.card := Finset.card_image_le
    have eq := identity S
    have exactPrice : price x E S=n+3*E.card-S.card := by omega
    rw [phys,exactPrice]
  · intro all p
    simpa [cov] using all K p

theorem criterion :
∀ (n m c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c) (x : Fin m → Fin n → Bool),
  (∀ e∈E, e.1<e.2) →
  (∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
    ∀ i k, color i=color k → (i∈V ↔ k∈V)) →
  (∀ j, ∃ a b, (∀ i, color i=j → x a i=false ∧ x b i=true) ∧
    (∀ i, color i≠j → x a i=x b i)) →
  ∀ K : Finset (Fin n), (∀ j, ∃! i, i∈K ∧ color i=j) →
  let F := (Fin n → Bool) → Bool
  let inv := fun (i : Fin n) (v : Fin n → Bool) => !(v i)
  let project := fun (f : F) (k : Fin m) => f (x k)
  let raw : Finset F := {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i v => v i) ∪
    E.image (fun e v => v e.1 == v e.2) ∪ E.image (fun e v => xor (v e.1) (v e.2))
  let targets : Finset F := Finset.univ.image inv ∪ E.image (fun e v => !(v e.1) && !(v e.2)) ∪
    E.image (fun e v => v e.1 && !(v e.2)) ∪ E.image (fun e v => !(v e.1) && v e.2)
  let demand := targets.image project
  let seeds := fun S : Finset (Fin n) => S.image (fun i => project (inv i))
  let bank := fun S => raw.image project ∪ seeds S
  let cost := fun S => (demand \ bank S).card
  let cover := fun (S : Finset (Fin n)) => ∀ j, ∃ i∈S, color i=j
  ∀ (inputs : Finset (Fin n) → List (Fin m → Bool)), (∀ S, (inputs S).toFinset=bank S) →
  let fits := fun S p =>
    let L := inputs S
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length D ∧ D.output<L.length+D.size ∧ D.size≤p ∧
      ∀ f∈demand, ∃ i<L.length+D.size, ∀ k, (D.wires (L.map (fun g => g k))).getD i false=f k
  (∀ S p, fits S p ↔ cover S ∧ cost S≤p) ∧
  (∀ S, cost S+(seeds S).card=cost K+K.card) ∧
  ((∀ p, fits K p ↔ n+3*E.card-K.card≤p) ↔ ∀ S p, fits S p ↔ cover S ∧ n+3*E.card-S.card≤p)
:= by
  intro n m c E color x sorted part pairs K one
  dsimp only
  intro inputs bankEq
  exact calibrate x color E sorted part pairs K one inputs bankEq

end

end PEqualNP.Outside.L_lib_1457.Core.GraphPriceCalibration

namespace PEqualNP.Outside.L_lib_1457.Core.GraphSampleDistance

noncomputable section
open Classical GraphInversionSeeds GraphPriceCalibration CircuitLowerBounds MetaComplexity

abbrev W (n : Nat) := Finset (Fin n)
abbrev asWord (f : F n) (u : W n) := f (fun i => decide (i ∈ u))
abbrev req (E : Finset (Edge n)) := (target E).image asWord
abbrev wire (E : Finset (Edge n)) (S : W n) := (GraphSeedSamples.bank E S).toList

def fitsAt (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) (p : Nat) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack (wire E S).length C ∧
    C.output < (wire E S).length+C.size ∧ C.size≤p ∧ ∀ f∈req E, ∃ j<(wire E S).length+C.size,
      ∀ u∈A, (C.wires ((wire E S).map (fun g => g u))).getD j false=f u

def keeps (A : Finset (W n)) (E : Finset (Edge n)) (color : Fin n → Fin c) :=
  ∀ S p, fitsAt A E S p ↔ GraphSeedSamples.cover color S ∧ n+3*E.card-S.card≤p

private theorem unbounded (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :
    GraphSeedSamples.fits A (wire E S) (req E) ↔ ∃ p, fitsAt A E S p := by
  constructor
  · rintro ⟨C,hm,hr,ho,hw⟩
    exact ⟨C.size,C,hm,hr,ho,le_rfl,hw⟩
  · rintro ⟨_,C,hm,hr,ho,_,hw⟩
    exact ⟨C,hm,hr,ho,hw⟩

private theorem asNeg (i : Fin n) : asWord (neg i) = GraphSeedSamples.inv i := by
  funext u
  simp [asWord,neg,GraphSeedSamples.inv]
private theorem asEq (e : Edge n) : asWord (eqBit e) = GraphSeedSamples.same e := by
  funext u
  by_cases a : e.1∈u <;> by_cases b : e.2∈u <;> simp [asWord,eqBit,GraphSeedSamples.same,a,b]
private theorem asXor (e : Edge n) : asWord (xorBit e) = GraphSeedSamples.cross e := by
  funext u
  by_cases a : e.1∈u <;> by_cases b : e.2∈u <;> simp [asWord,xorBit,GraphSeedSamples.cross,GraphSeedSamples.same,a,b]

private theorem wordBank (E : Finset (Edge n)) (S : W n) :
    GraphSeedSamples.bank E S = (raw E ∪ S.image neg).image asWord := by
  classical
  simp [GraphSeedSamples.bank,raw,Finset.image_union,Finset.image_image,Function.comp_def,
    asNeg,asEq,asXor]
  rfl

private theorem shape (E : Finset (Edge n)) (sorted : ∀ e∈E, e.1<e.2) :
    (target E).card = n+3*E.card := by
  classical
  have upper (X Y : Finset (F n)) := Finset.card_union_le X Y
  have a := upper (Finset.univ.image neg) (E.image zz)
  have b := upper (Finset.univ.image neg ∪ E.image zz) (E.image oz)
  have d := upper (Finset.univ.image neg ∪ E.image zz ∪ E.image oz) (E.image zo)
  have h1 := Finset.card_image_le (s:=E) (f:=zz)
  have h2 := Finset.card_image_le (s:=E) (f:=oz)
  have h3 := Finset.card_image_le (s:=E) (f:=zo)
  have hi := Finset.card_image_le (s:=(Finset.univ : Finset (Fin n))) (f:=neg)
  simp only [Finset.card_univ,Fintype.card_fin] at hi
  have lo := Finset.card_le_card (show target E \ raw E ⊆ target E from Finset.sdiff_subset)
  have eq := countTargets E sorted ∅
  simp only [Finset.image_empty,Finset.union_empty,Finset.card_empty,Nat.sub_zero] at eq
  unfold target at lo eq ⊢
  omega

private def enum (A : Finset (W n)) : Fin A.card ≃ A :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card A = A.card)).symm
private abbrev words (A : Finset (W n)) (k : Fin A.card) := (enum A k).val
private abbrev xrow (A : Finset (W n)) (k : Fin A.card) (i : Fin n) := decide (i∈words A k)
private abbrev readWord (A : Finset (W n)) (f : W n → Bool) (k : Fin A.card) := f (words A k)
private abbrev lines (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :=
  (wire E S).map (readWord A)

private theorem inputs (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) :
    (lines A E S).toFinset = GraphPriceCalibration.bank (xrow A) E S := by
  classical
  ext v
  simp only [lines,wire,List.mem_toFinset,List.mem_map,Finset.mem_toList,wordBank,
    Finset.mem_image,Finset.mem_union,GraphPriceCalibration.bank]
  constructor
  · rintro ⟨h,⟨f,hf,rfl⟩,rfl⟩
    rcases hf with hr|⟨i,hi,rfl⟩
    · exact Or.inl ⟨f,hr,rfl⟩
    · exact Or.inr ⟨i,hi,rfl⟩
  · rintro (⟨f,hr,rfl⟩|⟨i,hi,rfl⟩)
    · exact ⟨asWord f,⟨f,Or.inl hr,rfl⟩,rfl⟩
    · exact ⟨asWord (neg i),⟨_,Or.inr ⟨i,hi,rfl⟩,rfl⟩,rfl⟩

private theorem fitEq (A : Finset (W n)) (E : Finset (Edge n)) (S : W n) (p : Nat) :
    fitsAt A E S p ↔ sampleFits (lines A E S) (T (xrow A) E) p := by
  classical
  simp only [fitsAt,sampleFits,lines,List.length_map,sampleRow,List.map_map,Function.comp_def]
  constructor
  · rintro ⟨C,hm,hr,ho,hs,h⟩
    refine ⟨C,hm,hr,ho,hs,?_⟩
    rintro g hg
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨j,hj,v⟩ := h _ (Finset.mem_image_of_mem asWord hf)
    exact ⟨j,hj,fun k => v _ (enum A k).property⟩
  · rintro ⟨C,hm,hr,ho,hs,h⟩
    refine ⟨C,hm,hr,ho,hs,?_⟩
    rintro g hg
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨j,hj,v⟩ := h _ (Finset.mem_image_of_mem (proj (xrow A)) hf)
    refine ⟨j,hj,?_⟩
    intro u hu
    obtain ⟨k,hk⟩ := (enum A).surjective ⟨u,hu⟩
    have val := v k
    change (C.wires ((wire E S).map (fun g => g (enum A k).val))).getD j false =
      asWord f (enum A k).val at val
    simpa only [hk] using val

private theorem pureOfTested (A : Finset (W n)) (color : Fin n → Fin c)
    (h : GraphSeedSamples.tested A color) : pure (xrow A) color := by
  intro j
  obtain ⟨u,hu,dis,high⟩ := h j
  obtain ⟨a,ha⟩ := (enum A).surjective ⟨u,hu⟩
  obtain ⟨b,hb⟩ := (enum A).surjective ⟨u∪GraphSeedSamples.block color j,high⟩
  refine ⟨a,b,?_,?_⟩
  · intro i hi
    have mem : i∈GraphSeedSamples.block color j := by simp [GraphSeedSamples.block,hi]
    have missing : i∉u := fun hz => Finset.disjoint_left.mp dis hz mem
    simp [xrow,words,ha,hb,mem,missing]
  · intro i hi
    simp [xrow,words,ha,hb,GraphSeedSamples.block,hi]

def separates (A : Finset (W n)) (E : Finset (Edge n)) :=
  (∀ f∈target E, ∀ g∈target E, f≠g → ∃ u∈A, asWord f u≠asWord g u) ∧
  ∀ f∈target E, ∀ g∈raw E, ∃ u∈A, asWord f u≠asWord g u

private theorem rankTest (A : Finset (W n)) (E : Finset (Edge n)) :
    ((T (xrow A) E) \ R (xrow A) E).card = (target E).card ↔ separates A E := by
  classical
  let p := proj (xrow A)
  have agree (f g : F n) : p f = p g ↔ ∀ u∈A, asWord f u=asWord g u := by
    constructor
    · intro h u hu
      obtain ⟨k,hk⟩ := (enum A).surjective ⟨u,hu⟩
      have val := congrFun h k
      change asWord f (enum A k).val = asWord g (enum A k).val at val
      simpa only [hk] using val
    · intro h
      exact funext (fun k => h _ (enum A k).property)
  have alg : ((target E).image p \ (raw E).image p).card = (target E).card ↔
      Set.InjOn p (target E) ∧ Disjoint ((target E).image p) ((raw E).image p) := by
    constructor
    · intro h
      have small : (target E).image p \ (raw E).image p ⊆ (target E).image p := Finset.sdiff_subset
      have le := Finset.card_le_card small
      have upper := Finset.card_image_le (s:=target E) (f:=p)
      exact ⟨Finset.card_image_iff.mp (by omega), Finset.sdiff_eq_self_iff_disjoint.mp
        (Finset.eq_of_subset_of_card_le small (by omega))⟩
    · rintro ⟨inj,dis⟩
      rw [Finset.sdiff_eq_self_of_disjoint dis,Finset.card_image_of_injOn inj]
  change ((target E).image p \ (raw E).image p).card = (target E).card ↔ _
  rw [alg]
  constructor
  · rintro ⟨inj, dis⟩
    constructor
    · intro f hf g hg ne
      by_contra! h
      exact ne (inj hf hg ((agree _ _).mpr h))
    · intro f hf g hg
      by_contra! h
      exact Finset.disjoint_left.mp dis (Finset.mem_image_of_mem p hf)
        ((agree _ _).mpr h ▸ Finset.mem_image_of_mem p hg)
  · rintro ⟨diff,rawDiff⟩
    constructor
    · intro f hf g hg eq
      by_contra ne
      obtain ⟨u,hu,h⟩ := diff f hf g hg ne
      exact h ((agree _ _).mp eq u hu)
    · apply Finset.disjoint_left.mpr
      intro v ht hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨g,hg,eq⟩ := Finset.mem_image.mp hr
      obtain ⟨u,hu,h⟩ := rawDiff f hf g hg
      exact h ((agree _ _).mp eq.symm u hu)

theorem localTest (A : Finset (W n)) (E : Finset (Edge n)) (color : Fin n → Fin c)
    (onto : Function.Surjective color) (sorted : ∀ e∈E, e.1<e.2) (part : classes E color) :
    keeps A E color ↔ GraphSeedSamples.tested A color ∧ separates A E := by
  classical
  have testedOf (h : keeps A E color) : GraphSeedSamples.tested A color := by
    have reqInv (i : Fin n) : GraphSeedSamples.inv i ∈ req E := by
      rw [←asNeg]; exact Finset.mem_image_of_mem _ (by simp [target])
    apply ((GraphSeedSamples.criterion n c E color onto part (req E) reqInv).1 A).mp
    intro S
    change GraphSeedSamples.fits A (wire E S) (req E) ↔ GraphSeedSamples.cover color S
    rw [unbounded]
    constructor
    · rintro ⟨p,hp⟩
      exact ((h S p).mp hp).1
    · intro cov
      exact ⟨_,(h S _).mpr ⟨cov,le_rfl⟩⟩
  let rep (j : Fin c) := (onto j).choose
  have right (j : Fin c) : color (rep j)=j := (onto j).choose_spec
  let K := Finset.univ.image rep
  have transv (j : Fin c) : ∃! i, i∈K ∧ color i=j := by
    refine ⟨rep j,⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),right j⟩,?_⟩
    rintro v ⟨hv,hj⟩
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hv
    rw [right] at hj
    rw [hj]
  have cov : serves color K := fun j => ⟨_,(transv j).exists.choose_spec⟩
  have kc : K.card≤n := (Finset.card_le_univ K).trans (by simp)
  suffices work : ∀ t : GraphSeedSamples.tested A color, keeps A E color ↔ separates A E by
    exact ⟨fun h => ⟨testedOf h,(work (testedOf h)).mp h⟩,fun ⟨t,h⟩ => (work t).mpr h⟩
  intro test
  have cal := GraphPriceCalibration.criterion n A.card c E color (xrow A) sorted part
    (pureOfTested A color test) K transv (lines A E) (inputs A E)
  have pk (p : Nat) : sampleFits (lines A E K) (T (xrow A) E) p ↔
      price (xrow A) E K ≤ p := by
    exact (cal.1 K p).trans (and_iff_right cov)
  have rank := cal.2.1 ∅
  change price (xrow A) E ∅ + (N (xrow A) ∅).card = price (xrow A) E K + K.card at rank
  simp only [price,GraphPriceCalibration.bank,N,Finset.image_empty,Finset.union_empty,
    Finset.card_empty,Nat.add_zero] at rank
  rw [←rankTest,shape E sorted]
  constructor
  · intro h
    have small := (pk _).mpr le_rfl
    have lb := ((h K _).mp ((fitEq _ _ _ _).mpr small)).2
    have ub := (pk _).mp ((fitEq _ _ _ _).mp ((h K _).mpr ⟨cov,le_rfl⟩))
    change _ ≤ price (xrow A) E K at lb
    change price (xrow A) E K ≤ _ at ub
    change _ = price (xrow A) E K + K.card at rank
    omega
  · intro card
    have cost : price (xrow A) E K=n+3*E.card-K.card := by
      change _ = price (xrow A) E K + K.card at rank
      omega
    have all := cal.2.2.mp (fun p => (pk p).trans (by rw [cost]))
    intro S p
    exact (fitEq _ _ _ _).trans (all S p)

end
end PEqualNP.Outside.L_lib_1457.Core.GraphSampleDistance

namespace PEqualNP.Outside.L_lib_1457
open PEqualNP.Outside.L_lib_1457.Core
open GraphInversionSeeds GraphSampleDistance

abbrev Row (n : Nat) := Finset (Fin n)
abbrev Pairs (n : Nat) := {e : Fin n × Fin n // e.1 ≤ e.2}

def natbit (b : Bool) : Nat := if b then 1 else 0
def dif (x y : Bool) : Nat := if x=y then 0 else 1
def gap (x y : Nat) := (x-y)+(y-x)
def idx (p : Fin r → Row n) (i j : Fin n) (s : Fin r) := natbit (decide (i∈p s))+natbit (decide (j∈p s))
def md (p : Fin r → Row n) (i j k l : Fin n) := ∑ s, gap (idx p i j s) (idx p k l s)
def metric (p : Fin r → Row n) (d : Nat) := ∀ a b : Pairs n,a≠b → d < md p a.val.1 a.val.2 b.val.1 b.val.2

def low (i j : Fin n) : F n := fun x => !(x i) && !(x j)
def dir (i j : Fin n) : F n := fun x => x i && !(x j)
def blk (color : Fin n → Fin c) (j : Fin c) := Finset.univ.filter (fun i => color i=j)
def other (X : Row n) := Finset.univ \ X
def paired (p : Fin r → Row n) := List.ofFn p ++ List.ofFn (fun j => other (p j))
def anchors (color : Fin n → Fin c) (d : Nat) := List.replicate (d+1) (∅ : Row n) ++ (List.ofFn (fun j : Fin c => List.replicate (d+1) (blk color j))).flatten
def allRows (p : Fin r → Row n) (color : Fin n → Fin c) (d : Nat) := paired p ++ anchors color d

def freq (l : List α) (P : α → Bool) := l.countP P
def hd (l : List (Row n)) (f g : F n) := freq l (fun u => decide (asWord f u ≠ asWord g u))
def remaining (l : List α) [DecidableEq α] (Z : Finset (Fin l.length)) := (Finset.univ \ Z).image l.get

lemma freq_sum (p : Fin r → α) (P : α → Bool) : freq (List.ofFn p) P = ∑ s, (if P (p s) then 1 else 0) := by
  simp [freq,Finset.sum_boole]
lemma freq_indices (l : List α) (P : α → Bool) : freq l P = (Finset.univ.filter (fun i : Fin l.length => P (l.get i))).card := by
  simpa only [List.ofFn_get,freq] using List.countP_ofFn l.get P

lemma survive_iff [DecidableEq α] (l : List α) (P : α → Bool) (d : Nat) :
    (∀ Z : Finset (Fin l.length),Z.card≤d → ∃ x∈remaining l Z,P x=true) ↔ d<freq l P := by
  classical
  rw [freq_indices]
  let S := Finset.univ.filter (fun i : Fin l.length => P (l.get i))
  constructor
  · intro h; by_contra! hsmall
    obtain ⟨x,hx,yes⟩ := h S hsmall
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩)
  · intro h Z hz; have no : ¬ S ⊆ Z := fun inc => (Nat.not_lt_of_le ((Finset.card_le_card inc).trans hz)) h
    obtain ⟨i,hi,hiz⟩ := Finset.not_subset.mp no
    exact ⟨_,Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hiz⟩,rfl⟩,(Finset.mem_filter.mp hi).2⟩

lemma hd_pair (p : Fin r → Row n) (f g : F n) : hd (paired p) f g =
    ∑ j, (dif (asWord f (p j)) (asWord g (p j)) + dif (asWord f (other (p j))) (asWord g (other (p j)))) := by
  have part (q : Fin r → Row n) : (List.ofFn q).countP (fun u => decide (asWord f u ≠ asWord g u)) =
      ∑ j, dif (asWord f (q j)) (asWord g (q j)) := by
    apply (freq_sum q (fun u => decide (asWord f u ≠ asWord g u))).trans
    apply Finset.sum_congr rfl; intro j _
    by_cases h : asWord f (q j) = asWord g (q j) <;> simp [dif,h]
  rw [Finset.sum_add_distrib]; unfold paired hd freq; rw [List.countP_append]
  exact congrArg₂ Nat.add (part p) (part (fun j => other (p j)))

lemma hd_low (p : Fin r → Row n) (i j k l : Fin n) : hd (paired p) (low i j) (low k l)=md p i j k l := by
  rw [hd_pair]; apply Finset.sum_congr rfl; intro s _
  by_cases a : i∈p s <;> by_cases b : j∈p s <;> by_cases c : k∈p s <;> by_cases d : l∈p s <;> simp [low,asWord,other,idx,natbit,dif,gap,a,b,c,d]
lemma hd_direct (p : Fin r → Row n) (i j k l : Fin n) : hd (paired p) (dir i j) (dir k l)=md p i l k j := by
  rw [hd_pair]; apply Finset.sum_congr rfl; intro s _
  by_cases a : i∈p s <;> by_cases b : j∈p s <;> by_cases c : k∈p s <;> by_cases d : l∈p s <;> simp [dir,asWord,other,idx,natbit,dif,gap,a,b,c,d]

lemma md_swapL (p : Fin r → Row n) (i j k l : Fin n) : md p j i k l = md p i j k l := by
  unfold md; apply Finset.sum_congr rfl; intro s _; simp only [idx]; rw [Nat.add_comm (natbit (decide (j∈p s))) (natbit (decide (i∈p s)))]
lemma md_swapR (p : Fin r → Row n) (i j k l : Fin n) : md p i j l k = md p i j k l := by
  unfold md; apply Finset.sum_congr rfl; intro s _; simp only [idx]; rw [Nat.add_comm (natbit (decide (l∈p s))) (natbit (decide (k∈p s)))]

def pairKey (i j : Fin n) : Pairs n := ⟨(min i j,max i j),le_trans (min_le_left ..) (le_max_left ..)⟩
lemma key_cases (i j : Fin n) : (pairKey i j).val=(i,j) ∨ (pairKey i j).val=(j,i) := by
  rcases le_total i j with h|h <;> simp [pairKey,min_eq_left,min_eq_right,max_eq_left,max_eq_right,h]
lemma metric_for {p : Fin r → Row n} {d : Nat} (good : metric p d) {i j k l : Fin n}
    (no : ¬ ((i=k ∧ j=l) ∨ (i=l ∧ j=k))) : d<md p i j k l := by
  have ne : pairKey i j ≠ pairKey k l := by
    intro eq; have h := congrArg Subtype.val eq
    rcases key_cases i j with a|a <;> rcases key_cases k l with b|b <;> rw [a,b] at h <;> simp only [Prod.mk.injEq] at h <;> tauto
  have h := good _ _ ne
  rcases key_cases i j with a|a <;> rcases key_cases k l with b|b <;> rw [a,b] at h <;>
    first | exact h | exact (md_swapL p i j k l) ▸ h | exact (md_swapR p i j k l) ▸ h | simpa only [md_swapL p i j,md_swapR p _ _ k l] using h

end PEqualNP.Outside.L_lib_1457

namespace PEqualNP.Outside.L_lib_1457
open PEqualNP.Outside.L_lib_1457.Core GraphInversionSeeds GraphSampleDistance

lemma many {z : α} {l : List (List α)} {s : Nat} (h : List.replicate s z∈l) (P : α → Bool) (hp : P z=true) : s≤l.flatten.countP P := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.flatten_cons,List.countP_append]
    rcases List.mem_cons.mp h with e|e
    · subst a; simp [List.countP_replicate,hp]
    · exact (ih e).trans (Nat.le_add_left ..)

lemma anchor_freq (p : Fin r → Row n) (color : Fin n → Fin c) (d : Nat) (P : Row n → Bool)
    (yes : P ∅=true ∨ ∃ j,P (blk color j)=true) : d<freq (allRows p color d) P := by
  classical
  simp only [freq,allRows,anchors,List.countP_append,List.countP_replicate]
  rcases yes with h|⟨j,h⟩
  · simp [h]; omega
  · have mem : List.replicate (d+1) (blk color j) ∈ List.ofFn (fun j : Fin c => List.replicate (d+1) (blk color j)) := by simp
    have v := many mem P h; omega

lemma anchor_rows {p : Fin r → Row n} {color : Fin n → Fin c} {d : Nat}
    {Z : Finset (Fin (allRows p color d).length)} (hz : Z.card≤d) (u : Row n) (h : u=∅ ∨ ∃ j,u=blk color j) : u∈remaining (allRows p color d) Z := by
  have freq' : d<freq (allRows p color d) (fun x => decide (x=u)) := by
    apply anchor_freq
    rcases h with rfl|⟨j,rfl⟩; exact Or.inl (by simp); exact Or.inr ⟨j,by simp⟩
  obtain ⟨x,hx,he⟩ := (survive_iff _ _ _).mpr freq' Z hz
  exact of_decide_eq_true he ▸ hx

lemma from_hd {p : Fin r → Row n} {color : Fin n → Fin c} {d : Nat} {f g : F n}
    {Z : Finset (Fin (allRows p color d).length)} (hz : Z.card≤d) (big : d<hd (paired p) f g) :
    ∃ u∈remaining (allRows p color d) Z, asWord f u ≠ asWord g u := by
  have h : d<hd (allRows p color d) f g := by
    simp only [hd,allRows,freq,List.countP_append] at big ⊢; omega
  obtain ⟨x,hx,ok⟩ := (survive_iff _ _ _).mpr h Z hz
  exact ⟨x,hx,of_decide_eq_true ok⟩

lemma low_comm (a b : Fin n) : low a b = low b a := funext fun _ => Bool.and_comm ..
lemma low_ne_key {a b : Pairs n} (ab : a≠b) : low a.val.1 a.val.2 ≠ low b.val.1 b.val.2 := by
  intro eq
  have test (u v j : Fin n) : low u v (fun z => decide (j=z)) = false ↔ (j=u ∨ j=v) := by
    by_cases h : j=u <;> simp [low,h]
  have mem (j : Fin n) : (j=a.val.1 ∨ j=a.val.2) ↔ (j=b.val.1 ∨ j=b.val.2) := by
    rw [←test,←test,eq]
  apply ab; apply Subtype.ext; apply Prod.ext
  · have h1 := (mem a.val.1).mp (Or.inl rfl); have h2 := (mem b.val.1).mpr (Or.inl rfl); have h3:=a.property; have h4:=b.property; omega
  · have h1 := (mem a.val.2).mp (Or.inr rfl); have h2 := (mem b.val.2).mpr (Or.inr rfl); have h3:=a.property; have h4:=b.property; omega

lemma dir_even (p : Fin r → Row n) (i j : Fin n) (g : F n)
    (stable : ∀ s, asWord g (p s)=asWord g (other (p s))) : md p i i i j ≤ hd (paired p) (dir i j) g := by
  rw [hd_pair]; apply Finset.sum_le_sum; intro s _; rw [←stable s]
  cases h : asWord g (p s) <;> by_cases a : i∈p s <;> by_cases b : j∈p s <;> simp [asWord,dir,idx,other,natbit,gap,dif,h,a,b]

lemma shapeTarget {E : Finset (Edge n)} {f : F n} (hf : f∈target E) :
    (∃ i j, f=low i j ∧ (i=j ∨ (i,j)∈E)) ∨ (∃ i j, f=dir i j ∧ ((i,j)∈E ∨ (j,i)∈E)) := by
  simp only [target,Finset.mem_union,Finset.mem_image] at hf
  rcases hf with (((⟨i,_,rfl⟩|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)
  · exact Or.inl ⟨i,i,funext (by intro x; simp [low,neg]),Or.inl rfl⟩
  · exact Or.inl ⟨_,_,rfl,Or.inr he⟩
  · exact Or.inr ⟨_,_,rfl,Or.inl he⟩
  · exact Or.inr ⟨_,_,funext (fun x => Bool.and_comm ..),Or.inr he⟩

end PEqualNP.Outside.L_lib_1457

namespace PEqualNP.Outside.L_lib_1457
open PEqualNP.Outside.L_lib_1457.Core GraphInversionSeeds GraphSampleDistance

noncomputable def complete (n : Nat) : Finset (Edge n) := Finset.univ.filter (fun e => e.1<e.2)
def oneColor (_ : Fin n) : Fin 1 := 0

def promised (p : Fin r → Row n) (d : Nat) : Prop := ∀ (c : Nat) (E : Finset (Edge n)) (color : Fin n → Fin c),
  (∀ e∈E,e.1<e.2) → Function.Surjective color → GraphPriceCalibration.classes E color →
  ∀ Z : Finset (Fin (allRows p color d).length),Z.card≤d → keeps (remaining (allRows p color d) Z) E color

lemma complete_sorted : ∀ e∈complete n,e.1<e.2 := by intro e he; exact (Finset.mem_filter.mp he).2
lemma complete_classes : GraphPriceCalibration.classes (complete n) (@oneColor n) := by
  intro U; constructor
  · intro h i j _; rcases lt_trichotomy i j with hi|eq|hj
    · exact h (i,j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    · rw [eq]
    · exact (h (j,i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)).symm
  · intro h e _; exact h e.1 e.2 rfl

lemma lowTarget (a : Pairs n) : low a.val.1 a.val.2 ∈ target (complete n) := by
  classical
  rcases lt_or_eq_of_le a.property with lt|eq
  · have mem : a.val∈complete n := Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩
    unfold target
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem zz mem))))))
  · have same : low a.val.1 a.val.2=neg a.val.1 := by rw [eq]; funext x; simp [low,neg]
    rw [same]; simp [target]

lemma uniform_lows (p : Fin r → Row n) (d : Nat) (a b : Pairs n) :
    hd (allRows p oneColor d) (low a.val.1 a.val.2) (low b.val.1 b.val.2) = md p a.val.1 a.val.2 b.val.1 b.val.2 := by
  rw [←hd_low]
  let P := fun u : Row n => decide (asWord (low a.val.1 a.val.2) u ≠ asWord (low b.val.1 b.val.2) u)
  have he : P ∅=false := by simp [P,asWord,low]
  have hf : P Finset.univ=false := by simp [P,asWord,low]
  have hlist : (List.ofFn (fun j : Fin 1 => List.replicate (d+1) (blk (@oneColor n) j))).flatten = List.replicate (d+1) Finset.univ := by
    rw [List.ofFn_succ]; simp [blk,oneColor]
  change (paired p ++ anchors oneColor d).countP P = (paired p).countP P
  simp only [anchors,hlist,List.countP_append,List.countP_replicate,he,hf]
  simp

theorem necessary {p : Fin r → Row n} {d : Nat} (h : promised p d) : metric p d := by
  intro a b ne
  have sur : Function.Surjective (@oneColor n) := fun j => ⟨a.val.1,Subsingleton.elim ..⟩
  rw [←uniform_lows p d a b]
  apply (survive_iff _ _ _).mp
  intro Z hz
  have abs := (localTest _ _ _ sur complete_sorted complete_classes).mp (h 1 _ _ complete_sorted sur complete_classes Z hz)
  obtain ⟨x,hx,he⟩ := abs.2.1 _ (lowTarget a) _ (lowTarget b) (low_ne_key ne)
  exact ⟨x,hx,decide_eq_true he⟩

end PEqualNP.Outside.L_lib_1457

namespace PEqualNP.Outside.L_lib_1457
open PEqualNP.Outside.L_lib_1457.Core GraphInversionSeeds GraphSampleDistance

lemma edge_color {n c : Nat} {E : Finset (Edge n)} {color : Fin n → Fin c} (part : GraphPriceCalibration.classes E color)
    {i j : Fin n} (e : (i,j)∈E) : color i=color j := by
  have h := (part (blk color (color i))).mpr (by intro a b eq; simp [blk,eq]) (i,j) e
  simpa [blk,eq_comm] using h

lemma raw_shapes {E : Finset (Edge n)} {g : F n} (h : g∈raw E) :
    g=(fun _ => false) ∨ g=(fun _ => true) ∨ (∃ i,g=pos i) ∨ (∃ e∈E,g=eqBit e) ∨ ∃ e∈E,g=xorBit e := by
  simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,true_and] at h
  rcases h with ((((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩) <;> aesop

lemma separatedAt {n r c d : Nat} (p : Fin r → Row n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (sorted : ∀ e∈E,e.1<e.2) (part : GraphPriceCalibration.classes E color) (good : metric p d)
    (Z : Finset (Fin (allRows p color d).length)) (hz : Z.card≤d) : separates (remaining (allRows p color d) Z) E := by
  classical
  let A := remaining (allRows p color d) Z
  have empty : (∅ : Row n)∈A := anchor_rows hz _ (Or.inl rfl)
  have block (i : Fin n) : blk color (color i) ∈ A := anchor_rows hz _ (Or.inr ⟨_,rfl⟩)
  have via {u v : F n} (h : d<hd (paired p) u v) : ∃ x∈A,asWord u x≠asWord v x := from_hd hz h
  have edgeNe {i j : Fin n} (he : (i,j)∈E ∨ (j,i)∈E) : i≠j := by rintro rfl; rcases he with w|w <;> exact (lt_irrefl i) (sorted _ w)
  have blockSame {a b : Fin n} (h : a=b ∨ (a,b)∈E) : color b=color a := by rcases h with rfl|e; rfl; exact (edge_color part e).symm
  have drBlock {i j : Fin n} (e : (i,j)∈E ∨ (j,i)∈E) (k : Fin n) : asWord (dir i j) (blk color (color k))=false := by
    have eq : color i=color j := by rcases e with e|e; exact edge_color part e; exact (edge_color part e).symm
    by_cases h : color j=color k <;> simp [asWord,dir,blk,eq,h]
  constructor
  · intro f hf g hg ne
    rcases shapeTarget hf with ⟨i,j,rfl,ij⟩|⟨i,j,rfl,ij⟩ <;> rcases shapeTarget hg with ⟨k,l,rfl,kl⟩|⟨k,l,rfl,kl⟩
    · apply via; rw [hd_low]; apply metric_for good
      rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩); exact ne rfl; exact ne (low_comm ..)
    · exact ⟨∅,empty,by simp [asWord,dir,low]⟩
    · exact ⟨∅,empty,by simp [asWord,dir,low]⟩
    · apply via; rw [hd_direct]; apply metric_for good
      rintro (⟨rfl,rfl⟩|⟨h,_⟩); exact ne rfl; exact edgeNe ij h
  · intro f hf g hg
    rcases shapeTarget hf with ⟨i,j,rfl,ij⟩|⟨i,j,rfl,ij⟩
    · rcases raw_shapes hg with rfl|rfl|⟨k,rfl⟩|⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact ⟨∅,empty,by simp [asWord,low]⟩
      · exact ⟨_,block i,by simp [asWord,low,blk]⟩
      · exact ⟨∅,empty,by simp [asWord,low,pos]⟩
      · refine ⟨_,block i,?_⟩; have ee := edge_color part he
        by_cases hit : color e.2=color i <;> simp [asWord,low,eqBit,blk,ee,hit]
      · exact ⟨∅,empty,by simp [asWord,low,xorBit]⟩
    · have hmany : d<md p i i i j := metric_for good (by have := edgeNe ij; tauto)
      rcases raw_shapes hg with rfl|rfl|⟨k,rfl⟩|⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact via (hmany.trans_le (dir_even p i j _ (by intro; rfl)))
      · exact ⟨∅,empty,by simp [asWord,dir]⟩
      · refine ⟨_,block k,?_⟩; rw [drBlock ij k]; simp [asWord,pos,blk]
      · exact ⟨∅,empty,by simp [asWord,dir,eqBit]⟩
      · apply via; apply hmany.trans_le; apply dir_even; intro s
        by_cases a : e.1∈p s <;> by_cases b : e.2∈p s <;> simp [asWord,xorBit,other,a,b]

lemma sufficient {n c r d : Nat} (p : Fin r → Row n) (color : Fin n → Fin c) (E : Finset (Edge n))
    (sorted : ∀ e∈E,e.1<e.2) (onto : Function.Surjective color) (part : GraphPriceCalibration.classes E color)
    (good : metric p d) (Z : Finset (Fin (allRows p color d).length)) (hz : Z.card≤d) : keeps (remaining (allRows p color d) Z) E color := by
  apply (localTest _ E color onto sorted part).mpr
  refine ⟨?_,separatedAt p color E sorted part good Z hz⟩
  intro j
  refine ⟨∅,anchor_rows hz _ (Or.inl rfl),by simp,?_⟩
  simpa [GraphSeedSamples.block,blk] using anchor_rows hz _ (Or.inr ⟨j,rfl⟩)

end PEqualNP.Outside.L_lib_1457

namespace PEqualNP.Outside.L_lib_1457
open PEqualNP.Outside.L_lib_1457.Core GraphSampleDistance GraphInversionSeeds
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable section
open Classical
abbrev bit0 (i : Fin n) (x : Row n) := decide (i∈x)
abbrev neg0 (i : Fin n) (x : Row n) := !(bit0 i x)
abbrev same0 (e : Edge n) (x : Row n) := bit0 e.1 x == bit0 e.2 x

def raw0 (E : Finset (Edge n)) : Finset (Row n → Bool) :=
  {fun _ => false,fun _ => true} ∪ Finset.univ.image bit0 ∪ E.image same0 ∪ E.image (fun e x => !(same0 e x))
def need0 (E : Finset (Edge n)) : Finset (Row n → Bool) :=
  Finset.univ.image neg0 ∪ E.image (fun e x => neg0 e.1 x && neg0 e.2 x) ∪
      E.image (fun e x => bit0 e.1 x && neg0 e.2 x) ∪ E.image (fun e x => neg0 e.1 x && bit0 e.2 x)

lemma wire_eq (E : Finset (Edge n)) (S : Row n) : wire E S = (raw0 E ∪ S.image neg0).toList := by
  have hi : @GraphSeedSamples.inv n = neg0 := by funext i x; by_cases h : i∈x <;> simp [GraphSeedSamples.inv,neg0,bit0,h]
  have he : @GraphSeedSamples.same n = same0 := by
    funext e x; by_cases h : e.1∈x <;> by_cases k : e.2∈x <;> simp [GraphSeedSamples.same,same0,bit0,h,k]
  have hx : @GraphSeedSamples.cross n = (fun e x => !(same0 e x)) := by
    funext e x; unfold GraphSeedSamples.cross; rw [he]
  simp only [wire,GraphSeedSamples.bank,raw0,he,hx,hi] <;> rfl

lemma requests (E : Finset (Edge n)) : req E = need0 E := by
  simp only [req,target,need0,Finset.image_union,Finset.image_image,Function.comp_def]

lemma keeps_eq (A : Finset (Row n)) (E : Finset (Edge n)) (color : Fin n → Fin c) : keeps A E color ↔
    ∀ (S : Row n) (p : Nat), let L := (raw0 E ∪ S.image neg0).toList
      (∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧ C.output<L.length+C.size ∧ C.size≤p ∧
       ∀ f∈need0 E, ∃ j<L.length+C.size, ∀ x∈A,(C.wires (L.map (fun g => g x))).getD j false=f x) ↔
       (∀ j,∃ i∈S,color i=j) ∧ n+3*E.card-S.card≤p := by
  simp only [keeps,fitsAt,GraphSeedSamples.cover,wire_eq,requests]

def rowQual (l : List (Row n)) (E : Finset (Edge n)) (color : Fin n → Fin c) (d : Nat) : Prop :=
  ∀ Z : Finset (Fin l.length), Z.card≤d → keeps (remaining l Z) E color

def paperRows (probe : Fin r → Row n) (color : Fin n → Fin c) (d : Nat) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  List.ofFn probe ++ List.ofFn (fun j => Finset.univ \ probe j) ++ List.replicate (d+1) (∅ : Row n) ++
    (List.ofFn (fun j : Fin c => List.replicate (d+1) (Finset.univ.filter (fun i => color i=j)))).flatten

lemma row_eq (probe : Fin r → Row n) (color : Fin n → Fin c) (d : Nat) : allRows probe color d=paperRows probe color d := by
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  have beq : blk color = (fun j => Finset.univ.filter (fun i => color i=j)) := by
    funext j; ext i; simp [blk]
  have oeq : @other n = (fun x => Finset.univ \ x) := by funext x; ext i; simp [other]
  simp only [allRows,paired,anchors,paperRows,beq,oeq,List.append_assoc]

lemma paperSpec (p : Fin r → Row n) (d : Nat) : promised p d ↔ ∀ (c : Nat) (E : Finset (Edge n)) (color : Fin n → Fin c),
    (∀ e∈E,e.1<e.2) → Function.Surjective color → GraphPriceCalibration.classes E color → rowQual (paperRows p color d) E color d := by
  change (∀ (c : Nat) (E : Finset (Edge n)) (color : Fin n → Fin c), (∀ e∈E,e.1<e.2) → Function.Surjective color → GraphPriceCalibration.classes E color → rowQual (allRows p color d) E color d) ↔ _
  simp only [row_eq]

theorem characterized (p : Fin r → Row n) (d : Nat) : promised p d ↔ metric p d :=
  ⟨necessary,fun h _ E color sorted onto part Z hz => sufficient p color E sorted onto part h Z hz⟩

end
end PEqualNP.Outside.L_lib_1457

theorem PEqualNP.Outside.L_lib_1457 : (∀ (n r d : Nat) (probe : Fin r → Finset (Fin n)),
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  (∀ (c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
    (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
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
  let rows := List.ofFn probe ++ List.ofFn (fun j => Finset.univ \ probe j) ++
    List.replicate (d+1) (∅ : W) ++
    (List.ofFn (fun j : Fin c => List.replicate (d+1) (Finset.univ.filter (fun i => color i=j)))).flatten
  ∀ Z : Finset (Fin rows.length), Z.card≤d →
    keeps ((Finset.univ \ Z).image (fun i : Fin rows.length => rows.get i))) ↔
  let P := {p : Fin n × Fin n // p.1 ≤ p.2}
  let sum := fun (e : P) (j : Fin r) =>
    (if e.val.1 ∈ probe j then 1 else 0 : Nat) + (if e.val.2 ∈ probe j then 1 else 0)
  ∀ a b : P, a≠b → d < ∑ j : Fin r, ((sum a j - sum b j) + (sum b j - sum a j))) := by
  dsimp only
  intro n r d probe
  have h := PEqualNP.Outside.L_lib_1457.characterized probe d
  rw [PEqualNP.Outside.L_lib_1457.paperSpec] at h
  simp only [PEqualNP.Outside.L_lib_1457.rowQual,PEqualNP.Outside.L_lib_1457.paperRows,PEqualNP.Outside.L_lib_1457.keeps_eq,PEqualNP.Outside.L_lib_1457.Core.GraphPriceCalibration.classes,PEqualNP.Outside.L_lib_1457.remaining,PEqualNP.Outside.L_lib_1457.raw0,PEqualNP.Outside.L_lib_1457.need0,PEqualNP.Outside.L_lib_1457.bit0,PEqualNP.Outside.L_lib_1457.neg0,PEqualNP.Outside.L_lib_1457.same0,PEqualNP.Outside.L_lib_1457.metric,PEqualNP.Outside.L_lib_1457.md,PEqualNP.Outside.L_lib_1457.idx,PEqualNP.Outside.L_lib_1457.natbit,PEqualNP.Outside.L_lib_1457.gap,decide_eq_true_eq] at h
  have sd {α : Type} (i j : DecidableEq α) :
      (@Finset.instSDiff α i).sdiff = (@Finset.instSDiff α j).sdiff := by
    rw [Subsingleton.elim i j]
  convert! h using 1 <;> congr! 100
  exact sd _ _
