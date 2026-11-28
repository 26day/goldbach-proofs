import PEqualNP.Defs
import Mathlib.Order.Fin.Basic

namespace PEqualNP.Outside.L_lib_1474.Sign

inductive F (k : Nat) where
  | c (b : Bool)
  | lit (i : Fin k) (s : Bool)
  | gate (a : Bool) (l r : F k)
  deriving Inhabited

def op (a l r : Bool) := if a then l && r else l || r

def F.val {k} (f : F k) (x : Fin k → Bool) : Bool := match f with
  | .c b => b
  | .lit i s => x i == s
  | .gate a l r => op a (l.val x) (r.val x)

def F.cost {k} : F k → Nat
  | .c _ => 0
  | .lit _ _ => 1
  | .gate _ l r => l.cost+r.cost

def F.occ {k} (j : Fin k) (b : Bool) : F k → Nat
  | .c _ => 0
  | .lit i s => if i=j ∧ s=b then 1 else 0
  | .gate _ l r => l.occ j b + r.occ j b

def F.edit {k} (j : Fin k) (b v : Bool) : F k → F k
  | .c z => .c z
  | .lit i s => if i=j ∧ s=b then .c v else .lit i s
  | .gate a l r => .gate a (l.edit j b v) (r.edit j b v)

theorem edit_cost {k} (f : F k) (j : Fin k) (b v : Bool) :
    (f.edit j b v).cost + f.occ j b = f.cost := by
  induction f with
  | c => rfl
  | lit => simp only [F.edit,F.occ]; split <;> simp [F.cost]
  | gate a l r hl hr => simp only [F.cost,F.edit,F.occ]; omega

theorem edit_none {k} (f : F k) (j : Fin k) (b v : Bool) (zero : f.occ j b=0) :
    f.edit j b v = f := by
  induction f with
  | c => rfl
  | lit => simp only [F.edit,F.occ] at *; split at * <;> simp_all
  | gate a l r hl hr => simp only [F.occ,Nat.add_eq_zero_iff] at zero; simp [F.edit,hl zero.1,hr zero.2]

theorem literal_set {k} (j : Fin k) (x : Fin k → Bool) (b v : Bool) (f : F k)
    (h : f.occ j (!b) = 0) : (f.edit j b v).val x = f.val (Function.update x j (v == b)) := by
  induction f with
  | c => rfl
  | lit i s =>
    by_cases hj : i=j
    · subst i; cases b <;> cases v <;> cases s <;> simp_all [F.edit,F.val,F.occ]
    · simp [F.edit,F.val,hj,Function.update_of_ne hj]
  | gate a l r hl hr => simp only [F.occ,Nat.add_eq_zero_iff] at h; simp [F.edit,F.val,hl h.1,hr h.2]

theorem unchanged {k} (j : Fin k) (x : Fin k → Bool) (b : Bool) (f : F k)
    (hp : f.occ j true = 0) (hn : f.occ j false = 0) :
    f.val (Function.update x j b) = f.val x := by
  simpa [edit_none f j true b hp] using (literal_set j x true b f hn).symm

theorem edit_same {k} (f : F k) (j : Fin k) (x : Fin k → Bool) (b : Bool) :
    (f.edit j b (x j == b)).val x = f.val x := by
  induction f with
  | c => rfl
  | lit i s => by_cases h : i=j ∧ s=b <;> simp only [F.edit,if_pos,if_neg,h,F.val] <;> simp_all <;> rfl
  | gate a l r hl hr => simp [F.edit,F.val,hl,hr]

theorem eval_mono (a : Bool) {l r l' r' : Bool} (hl : l ≤ l') (hr : r ≤ r') : op a l r ≤ op a l' r' := by
  revert hl hr; cases a <;> cases l <;> cases r <;> cases l' <;> cases r' <;> decide

theorem edit_le {k} (f : F k) (j : Fin k) (x : Fin k → Bool) (b : Bool) :
    (f.edit j b false).val x ≤ f.val x ∧ f.val x ≤ (f.edit j b true).val x := by
  induction f with
  | c => exact ⟨le_rfl,le_rfl⟩
  | lit i s => by_cases h : i=j ∧ s=b <;> simp [F.edit,F.val,h]
  | gate a l r hl hr => exact ⟨eval_mono a hl.1 hr.1,eval_mono a hl.2 hr.2⟩

def Witness {k} (f : F k) (j : Fin k) (v : Bool) := ∀ x,
    (f.edit j false v).val x = f.val x ∨
    (f.edit j false v).val x = f.val (Function.update x j (!v))

theorem mixed_binary (a l r t u w : Bool) (bound : if a then w ≤ op a l r else op a l r ≤ w)
    (mix : w = op a t r ∨ w = op a l u) : w = op a l r ∨ w = op a t u := by
  revert bound mix; cases a <;> cases l <;> cases r <;> cases t <;> cases u <;> cases w <;> decide

theorem split_edit {k} (l r : F k) (j : Fin k) (a : Bool)
    (sp : (l.occ j true = 0 ∧ r.occ j false = 0) ∨ (r.occ j true = 0 ∧ l.occ j false = 0)) :
    Witness (.gate a l r) j (!a) := by
  intro x
  let w := ((F.gate a l r).edit j false (!a)).val x
  apply mixed_binary a (l.val x) (r.val x) (l.val (Function.update x j (!!a))) (r.val (Function.update x j (!!a))) w
  · cases a
    · exact (edit_le (.gate false l r) j x false).2
    · exact (edit_le (.gate true l r) j x false).1
  · dsimp [w,F.edit,F.val]; rcases sp with ⟨hl,hr⟩ | ⟨hr,hl⟩
    · left; rw [edit_none r j false (!a) hr,literal_set j x false (!a) l hl]; cases a <;> rfl
    · right; rw [edit_none l j false (!a) hl,literal_set j x false (!a) r hr]; cases a <;> rfl

theorem sparse_edit {k} (f : F k) (j : Fin k) (hp : f.occ j true ≤ 1) (hn : f.occ j false ≤ 1) :
    ∃ v, Witness f j v := by
  by_cases z : f.occ j false = 0
  · exact ⟨true,fun x => Or.inl (by rw [edit_none f j false true z])⟩
  by_cases t : f.occ j true = 0
  · exact ⟨true,fun x => Or.inr (literal_set j x false true f t)⟩
  induction f with
  | c => simp [F.occ] at z
  | lit i s => cases s <;> simp [F.occ] at z t
  | gate a l r il ir =>
    simp only [F.occ] at hp hn z t
    by_cases pl : l.occ j true=0 <;> by_cases nl : l.occ j false=0
    · obtain ⟨v,hv⟩ := ir (by omega) (by omega) (by omega) (by omega)
      refine ⟨v,fun x => ?_⟩
      rcases hv x with h | h
      · left; simp [F.edit,F.val,edit_none l j false v nl,h]
      · right; simp [F.edit,F.val,edit_none l j false v nl,h,unchanged j x (!v) l pl nl]
    · exact ⟨!a,split_edit l r j a (Or.inl ⟨pl,by omega⟩)⟩
    · exact ⟨!a,split_edit l r j a (Or.inr ⟨by omega,nl⟩)⟩
    · have pr : r.occ j true=0 := by omega
      have nr : r.occ j false=0 := by omega
      obtain ⟨v,hv⟩ := il (by omega) (by omega) nl pl
      refine ⟨v,fun x => ?_⟩
      rcases hv x with h | h
      · left; simp [F.edit,F.val,edit_none r j false v nr,h]
      · right; simp [F.edit,F.val,edit_none r j false v nr,h,unchanged j x (!v) r pr nr]

def weight {k} (H : Finset (Fin k)) (x : Fin k → Bool) (b : Bool) := (H.filter (fun i => x i = b)).card
def Safe {k} (H : Finset (Fin k)) (f : F k) (p q : Nat) := ∀ x,
    (f.val x = true → p ≤ weight H x true) ∧ (f.val x = false → q ≤ weight H x false)

theorem weight_update {k} (H : Finset (Fin k)) (x : Fin k → Bool) (j : Fin k) (b : Bool) :
    weight H (Function.update x j b) (!b) ≤ weight H x (!b) ∧
    weight H (Function.update x j b) b ≤ weight H x b + 1 := by
  constructor
  · apply Finset.card_le_card; intro i hi; simp only [Finset.mem_filter] at *; by_cases eq : i=j <;> simp_all [Function.update_of_ne]
  · apply le_trans (b := (insert j (H.filter (fun i => x i = b))).card)
    · apply Finset.card_le_card; intro i hi; by_cases eq : i=j <;> simp_all [Function.update_of_ne]
    · exact Finset.card_insert_le ..

theorem safe_edit {k} {H : Finset (Fin k)} {f : F k} {j : Fin k} {p q : Nat} {v : Bool}
    (safe : Safe H f p q) (w : Witness f j v) : Safe H (f.edit j false v) p q := by
  intro x
  have s := safe x
  have u := safe (Function.update x j (!v))
  have he := w x
  have mono := edit_le f j x false
  have wt := (weight_update H x j (!v)).1
  cases v
  · constructor
    · intro h; exact s.1 (le_antisymm (Bool.le_true _) (h ▸ mono.1))
    · intro h; rcases he with e | e
      · exact s.2 (e ▸ h)
      · exact (u.2 (e ▸ h)).trans wt
  · constructor
    · intro h; rcases he with e | e
      · exact s.1 (e ▸ h)
      · exact (u.1 (e ▸ h)).trans wt
    · intro h; exact s.2 (le_antisymm (h ▸ mono.2) (Bool.false_le _))

theorem other_occ {k} (f : F k) (j : Fin k) (v b : Bool) :
    (f.edit j b v).occ j (!b) = f.occ j (!b) := by
  induction f with
  | c => rfl
  | lit i s => by_cases h : i=j ∧ s=b <;> simp [F.edit,h,F.occ] <;> rcases h with ⟨rfl,rfl⟩ <;> cases b <;> rfl
  | gate a l r hl hr => simp [F.edit,F.occ,hl,hr]

theorem eval_fixed {k} (f : F k) (j : Fin k) (v : Bool) (x : Fin k → Bool) :
    ((f.edit j true v).edit j false (!v)).val x = f.val (Function.update x j v) := by
  induction f with
  | c => rfl
  | lit i s => by_cases eq : i=j <;> cases s <;> simp [F.edit,F.val,eq,Function.update_of_ne]
  | gate a l r hl hr => simp [F.edit,F.val,hl,hr]

def Forces {k} (f : F k) (b : Bool) (s : Finset (Fin k)) := ∀ x : Fin k → Bool, (∀ i ∈ s, x i=b) → f.val x=b
def Cert {k} (f : F k) := ∃ S T : Finset (Fin k), Forces f true S ∧ Forces f false T ∧ S.card*T.card ≤ f.cost
theorem combine {k} {l r : F k} (a : Bool) (hl : Cert l) (hr : Cert r) : Cert (.gate a l r) := by
  obtain ⟨S,T,s,t,lc⟩ := hl
  obtain ⟨U,V,u,v,rc⟩ := hr
  have wu := Finset.card_union_le S U
  have wv := Finset.card_union_le T V
  cases a
  · let W := if S.card ≤ U.card then S else U
    refine ⟨W,T ∪ V,?_,?_,?_⟩
    · intro x h; dsimp [W] at h; split at h <;> first | simp [F.val,op,s x h] | simp [F.val,op,u x h]
    · intro x h; simp [F.val,op,t x (fun i hi => h i (Finset.mem_union_left _ hi)),v x (fun i hi => h i (Finset.mem_union_right _ hi))]
    · change W.card*_ ≤ l.cost+r.cost; have hs : W.card ≤ S.card := by dsimp [W]; split <;> omega
      have hu : W.card ≤ U.card := by dsimp [W]; split <;> omega
      calc
        _ ≤ W.card*(T.card+V.card) := Nat.mul_le_mul_left _ wv
        _ ≤ S.card*T.card+U.card*V.card := by rw [Nat.mul_add]; exact Nat.add_le_add (Nat.mul_le_mul_right _ hs) (Nat.mul_le_mul_right _ hu)
        _ ≤ _ := Nat.add_le_add lc rc
  · let W := if T.card ≤ V.card then T else V
    refine ⟨S ∪ U,W,?_,?_,?_⟩
    · intro x h; simp [F.val,op,s x (fun i hi => h i (Finset.mem_union_left _ hi)),u x (fun i hi => h i (Finset.mem_union_right _ hi))]
    · intro x h; dsimp [W] at h; split at h <;> first | simp [F.val,op,t x h] | simp [F.val,op,v x h]
    · change _*W.card ≤ l.cost+r.cost; have ht : W.card ≤ T.card := by dsimp [W]; split <;> omega
      have hv : W.card ≤ V.card := by dsimp [W]; split <;> omega
      calc
        _ ≤ (S.card+U.card)*W.card := Nat.mul_le_mul_right _ wu
        _ ≤ S.card*T.card+U.card*V.card := by rw [Nat.add_mul]; exact Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hv)
        _ ≤ _ := Nat.add_le_add lc rc

def Clean {k} (f : F k) := (∃ b, ∀ x, f.val x=b) ∨ Cert f
theorem transport {k} {f g : F k} (h : ∀ x, f.val x=g.val x) (le : g.cost≤f.cost) : Clean g → Clean f := by
  rintro (⟨b,hb⟩|⟨S,T,s,t,c⟩)
  · exact Or.inl ⟨b,fun x => (h x).trans (hb x)⟩
  · exact Or.inr ⟨S,T,fun x hx => (h x).trans (s x hx),fun x hx => (h x).trans (t x hx),c.trans le⟩
theorem clean_gate {k} (a : Bool) (l r : F k) (hl : Clean l) (hr : Clean r) : Clean (.gate a l r) := by
  rcases hl with ⟨b,h⟩|cl
  · cases a <;> cases b
    · exact transport (g := r) (by intro x; simp [F.val,op,h]) (Nat.le_add_left ..) hr
    · exact Or.inl ⟨true,fun x => by simp [F.val,op,h]⟩
    · exact Or.inl ⟨false,fun x => by simp [F.val,op,h]⟩
    · exact transport (g := r) (by intro x; simp [F.val,op,h]) (Nat.le_add_left ..) hr
  rcases hr with ⟨b,h⟩|cr
  · cases a <;> cases b
    · exact transport (g := l) (by intro x; simp [F.val,op,h]) (Nat.le_add_right ..) (Or.inr cl)
    · exact Or.inl ⟨true,fun x => by simp [F.val,op,h]⟩
    · exact Or.inl ⟨false,fun x => by simp [F.val,op,h]⟩
    · exact transport (g := l) (by intro x; simp [F.val,op,h]) (Nat.le_add_right ..) (Or.inr cl)
  exact Or.inr (combine a cl cr)
theorem clean_positive {k} (f : F k) (pos : ∀ j, f.occ j false=0) : Clean f := by
  induction f with
  | c b => exact Or.inl ⟨b,fun x => rfl⟩
  | lit i s =>
    have h := pos i; cases s
    · simp [F.occ] at h
    · refine Or.inr ⟨{i},{i},?_,?_,by simp [F.cost]⟩ <;> intro x hx <;> simp [F.val,hx i (by simp)]
  | gate a l r il ir =>
    apply clean_gate a l r
    · apply il; intro j; have := pos j; simp only [F.occ,Nat.add_eq_zero_iff] at this; exact this.1
    · apply ir; intro j; have := pos j; simp only [F.occ,Nat.add_eq_zero_iff] at this; exact this.2

theorem clean_bound {k} (H : Finset (Fin k)) (f : F k) (p q : Nat) (safe : Safe H f p q) (c : Clean f) : p*q≤f.cost := by
  rcases c with ⟨b,h⟩|⟨S,T,s,t,le⟩
  · cases b
    · have hq := (safe (fun _ => true)).2 (h _); simp [weight] at hq; simp [hq]
    · have hp := (safe (fun _ => false)).1 (h _); simp [weight] at hp; simp [hp]
  · let x := fun i => decide (i ∈ S)
    let y := fun i => decide (i ∉ T)
    have hp := (safe x).1 (s x (by simp [x]))
    have hq := (safe y).2 (t y (by simp [y]))
    apply le_trans _ le
    apply Nat.mul_le_mul (hp.trans _) (hq.trans _)
    · apply Finset.card_le_card; intro i; simp [x]
    · apply Finset.card_le_card; intro i; simp [y]

end PEqualNP.Outside.L_lib_1474.Sign

namespace PEqualNP.Outside.L_lib_1474
open PEqualNP.CircuitLowerBounds

theorem parallelFold {α β} {R : α → β → Prop} (d : α) (e : β) (de : R d e)
    (f : List α → Gate → α) (g : List β → Gate → β) (P : Gate → Prop)
    (step : ∀ a b, (∀ i, R (a.getD i d) (b.getD i e)) → ∀ t, P t → R (f a t) (g b t))
    (ts : List Gate) (ok : ∀ t ∈ ts, P t) (a : List α) (b : List β)
    (hlen : a.length = b.length) (h : ∀ i, R (a.getD i d) (b.getD i e)) : ∀ i,
    R ((ts.foldl (fun u t => u ++ [f u t]) a).getD i d)
      ((ts.foldl (fun u t => u ++ [g u t]) b).getD i e) := by
  induction ts generalizing a b with
  | nil => exact h
  | cons t ts ih =>
    apply ih (fun z hz => ok z (by simp [hz])) _ _ (by simp [hlen])
    intro i
    rcases lt_trichotomy i a.length with lt | eq | gt
    · have lt' : i < b.length := hlen ▸ lt
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_append_left lt'] using h i
    · subst i; simpa [List.getD_eq_getElem?_getD,List.getElem?_append,hlen] using step a b h t (ok t (by simp))
    · have q : a.length ≤ i := by omega
      have q' : b.length ≤ i := by omega
      have z : i-a.length ≠ 0 := by omega
      simpa [List.getD_eq_getElem?_getD,List.getElem?_append, Nat.not_lt.mpr q,Nat.not_lt.mpr q',← hlen,z] using de

open Classical in
noncomputable def countG (zs : List (Nat × Nat)) (g : Gate) :=
  let ab := g.inputs.foldl (fun (acc : Nat × Nat) j => let z := zs.getD j (0,0); (acc.1+z.1,acc.2+z.2)) (0,0)
  let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
  if g.op=.not then (h.2,h.1) else ab
open Classical in
noncomputable def timeG (ts : List Nat) (g : Gate) :=
  let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
  if g.op=.not then (g.inputs.head?.map (fun j => ts.getD j 0)).getD 0
  else mx+(if g.op=.and then 1 else 1)


end PEqualNP.Outside.L_lib_1474
namespace PEqualNP.Outside.L_lib_1474.Sign
open PEqualNP.CircuitLowerBounds

def F.flip {k} : F k → F k
  | .c b => .c (!b)
  | .lit j s => .lit j (!s)
  | .gate a l r => .gate (!a) l.flip r.flip
theorem flip_cost {k} (f : F k) : f.flip.cost = f.cost := by induction f <;> simp_all [F.cost,F.flip]
theorem flip_val {k} (f : F k) (x : Fin k → Bool) : f.flip.val x = !(f.val x) := by
  induction f with
  | c => rfl
  | lit i s => cases s <;> cases h : x i <;> simp [F.flip,F.val,h]
  | gate a l r il ir => cases a <;> simp [F.flip,F.val,op,il,ir]
def fg {k} (w : List (F k)) (g : Gate) : F k :=
  let atI := fun i => w.getD i (.c false)
  let comb := fun a => match g.inputs with
    | [] => .c a | [i] => atI i | i::j::_ => .gate a (atI i) (atI j)
  match g.op with
  | .not => ((g.inputs.head?.map atI).getD (.c false)).flip
  | .and => comb true | _ => comb false
def bg (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem fg_eval {k} (x : Fin k → Bool) (a : List (F k)) (b : List Bool)
    (eq : ∀ i, (a.getD i (.c false)).val x = b.getD i false) (g : Gate)
    (ok : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    (fg a g).val x = bg b g := by
  simp only [List.getD_eq_getElem?_getD] at eq
  obtain ⟨o,is⟩ := g; rcases ok with ⟨ok,le⟩; rcases ok with rfl|rfl|rfl <;>
    cases is with
    | nil => rfl
    | cons i is =>
      cases is with
      | nil => simp [fg,bg,F.val,op,GateOp.eval,flip_val,eq]
      | cons j rest =>
        have e : rest=[] := by simpa using le
        subst rest; simp [fg,bg,F.val,op,GateOp.eval,flip_val,eq]

def sums (c : Nat × Nat) := c.1+c.2
def cs {k} (H : Finset (Fin k)) := List.ofFn (fun j : Fin k => ((if j∈H then 1 else 0,0) : Nat × Nat)) ++ [(0,0),(0,0)]
noncomputable def cnt {k} (H : Finset (Fin k)) (D : Circuit) := (D.gates.foldl (fun zs g => zs ++ [countG zs g]) (cs H)).getD D.output (0,0)

theorem fg_count {k} (a : List (F k)) (b : List (Nat × Nat))
    (le : ∀ i, (a.getD i (.c false)).cost ≤ sums (b.getD i (0,0))) (g : Gate)
    (ok : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    (fg a g).cost ≤ sums (countG b g) := by
  obtain ⟨o,is⟩ := g; rcases ok with ⟨ok,sz⟩; rcases ok with rfl|rfl|rfl <;>
    cases is with
    | nil => simp [fg,F.flip,F.cost]
    | cons i is =>
      have hi := le i
      cases is with
      | nil => simp [fg,F.cost,countG,flip_cost,sums] <;> simp only [sums,List.getD_eq_getElem?_getD] at * <;> omega
      | cons j rest =>
        have e : rest=[] := by simpa using sz
        subst rest; have hj := le j
        simp [fg,F.cost,countG,flip_cost,sums] <;> simp only [sums,List.getD_eq_getElem?_getD] at * <;> omega
def seed {k} (A B : Finset (Fin k)) (j : Fin k) : F k := if j∈A then .c true else if j∈B then .lit j true else .c false
def ys {k} (A B : Finset (Fin k)) (x : Fin k → Bool) := A ∪ ((B \ A).filter (fun i => x i = true))
theorem fg_time {k} (a : List (F k)) (b : List Nat)
    (le : ∀ i, (a.getD i (.c false)).cost ≤ 2^b.getD i 0) (g : Gate)
    (ok : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    (fg a g).cost ≤ 2^(timeG b g) := by
  obtain ⟨o,is⟩ := g; rcases ok with ⟨ok,sz⟩; rcases ok with rfl|rfl|rfl <;>
    cases is with
    | nil => simp [fg,F.flip,F.cost]
    | cons i is =>
      have hi := le i
      cases is with
      | nil => simp [fg,F.cost,timeG,flip_cost,Nat.pow_succ] <;> simp only [List.getD_eq_getElem?_getD] at * <;> omega
      | cons j rest =>
        have e : rest=[] := by simpa using sz
        subst rest; have hj := le j
        have mi : 2^(b.getD i 0) ≤ 2^max (b.getD i 0) (b.getD j 0) := Nat.pow_le_pow_right (by decide) (le_max_left ..)
        have mj : 2^(b.getD j 0) ≤ 2^max (b.getD i 0) (b.getD j 0) := Nat.pow_le_pow_right (by decide) (le_max_right ..)
        simp [fg,F.cost,timeG,flip_cost,Nat.pow_succ] <;> simp only [List.getD_eq_getElem?_getD] at * <;> omega

end PEqualNP.Outside.L_lib_1474.Sign

namespace PEqualNP.Outside.L_lib_1474.Sign

def F.hit {k} (f : F k) (j : Fin k) := f.occ j true + f.occ j false

lemma hit_flip {k} (f : F k) (j : Fin k) : f.flip.hit j = f.hit j := by
  induction f with
  | c => rfl
  | lit i s => cases s <;> by_cases e : i=j <;> simp [F.flip,F.hit,F.occ,e]
  | gate a l r hl hr => simp only [F.hit,F.flip,F.occ] at *; omega

lemma occ_edit {k} (f : F k) (j i : Fin k) (b v s : Bool) :
    (f.edit j b v).occ i s = if i=j ∧ s=b then 0 else f.occ i s := by
  induction f with
  | c => simp [F.edit,F.occ]
  | lit t z =>
    by_cases h : t=j ∧ z=b
    · rcases h with ⟨rfl,rfl⟩
      simp only [F.edit,and_self,ite_true,F.occ]
      split_ifs <;> grind
    · simp only [F.edit,if_neg h,F.occ]
      by_cases e : i=j ∧ s=b
      · rcases e with ⟨rfl,rfl⟩; simp [h]
      · rw [if_neg e]
  | gate a l r hl hr => simp only [F.edit,F.occ,hl,hr]; split <;> simp

lemma edit_le_hits {k} (f : F k) (j i : Fin k) (b v : Bool) : (f.edit j b v).hit i ≤ f.hit i := by
  simp only [F.hit,occ_edit]; split_ifs <;> omega

lemma weighted {k} (H U : Finset (Fin k)) (f : F k) (p q C : Nat) (w : Fin k → Nat)
    (sm : min p q ≤ C+2) (safe : Safe H f p q)
    (localPins : ∀ i, i ∉ U → f.hit i=0) (bound : ∀ i, f.hit i ≤ w i) :
    2*(p*q) ≤ 2*f.cost + C*(U.sum (fun i => w i-1)) := by
  by_cases neg : ∃ j, f.occ j false ≠ 0
  · obtain ⟨j,hj⟩ := neg
    by_cases heavy : 3 ≤ f.hit j
    · let v := decide (q ≤ p)
      let g := (f.edit j true v).edit j false (!v)
      have cc : g.cost+f.hit j=f.cost := by
        have a := edit_cost f j true v
        have b := edit_cost (f.edit j true v) j false (!v)
        rw [occ_edit] at b
        simp only [Bool.false_eq_true,and_false,if_false] at b
        dsimp only [g,F.hit]; omega
      have dec : g.cost<f.cost := by omega
      have jU : j∈U := by by_contra h; have := localPins j h; omega
      have single : g.hit j = 0 := by simp [g,F.hit,occ_edit]
      have le (i : Fin k) : g.hit i ≤ f.hit i := (edit_le_hits _ _ _ _ _).trans (edit_le_hits ..)
      have loc (i : Fin k) (no : i∉U.erase j) : g.hit i=0 := by
        by_cases e : i=j
        · simpa only [e] using single
        · have nh : i∉U := fun hi => no (Finset.mem_erase.mpr ⟨e,hi⟩)
          exact Nat.eq_zero_of_le_zero ((le i).trans (localPins i nh).le)
      have cap (i : Fin k) : g.hit i ≤ w i := (le i).trans (bound i)
      have eq := Finset.sum_erase_add U (fun i => w i-1) jU
      have pay : C*2 ≤ C*(w j-1) := Nat.mul_le_mul_left _ (by have := bound j; omega)
      have liftBound {x t : Nat} (ih : 2*x ≤ 2*g.cost+C*((U.erase j).sum (fun i => w i-1)))
          (prod : p*q=x+t) (small : t≤C+2) : 2*(p*q) ≤ 2*f.cost+C*(U.sum (fun i => w i-1)) := by
        rw [prod,← eq,Nat.mul_add C]; omega
      by_cases cmp : q ≤ p
      · have veq : v=true := by simp [v,cmp]
        have hs : Safe H g (p-1) q := by
          intro x; have s := safe (Function.update x j true); have wt := weight_update H x j true
          simp only [g,eval_fixed,veq]; exact ⟨fun h => by have := s.1 h; omega,fun h => (s.2 h).trans wt.1⟩
        have ih := weighted H (U.erase j) g (p-1) q C w (by omega) hs loc cap
        cases p with
        | zero => simp
        | succ p => exact liftBound (t := q) ih (by simp [Nat.succ_mul]) (by omega)
      · have veq : v=false := by simp [v,cmp]
        have hs : Safe H g p (q-1) := by
          intro x; have s := safe (Function.update x j false); have wt := weight_update H x j false
          simp only [g,eval_fixed,veq]; exact ⟨fun h => (s.1 h).trans wt.1,fun h => by have := s.2 h; omega⟩
        have ih := weighted H (U.erase j) g p (q-1) C w (by omega) hs loc cap
        cases q with
        | zero => simp
        | succ q => exact liftBound (t := p) ih (by simp [Nat.mul_succ]) (by omega)
    · have hsmall : f.occ j true + f.occ j false < 3 := Nat.lt_of_not_ge heavy
      have ex : ∃ v, Witness f j v := by
        by_cases nonePos : f.occ j true=0
        · exact ⟨true,fun x => Or.inr (literal_set j x false true f nonePos)⟩
        · exact sparse_edit f j (by omega) (by omega)
      obtain ⟨v,hv⟩ := ex
      have cost := edit_cost f j false v
      have dec : (f.edit j false v).cost < f.cost := by omega
      have ih := weighted H U (f.edit j false v) p q C w sm (safe_edit safe hv)
        (fun i hi => Nat.eq_zero_of_le_zero ((edit_le_hits ..).trans (localPins i hi).le))
        (fun i => (edit_le_hits ..).trans (bound i))
      omega
  · have := clean_bound H f p q safe (clean_positive f (by simpa using neg)); omega
termination_by f.cost

end PEqualNP.Outside.L_lib_1474.Sign

namespace PEqualNP.Outside.L_lib_1474.Sign
open PEqualNP.CircuitLowerBounds

lemma hit_c {k} (b : Bool) (x : Fin k) : (F.c b).hit x=0 := rfl
lemma hit_lit {k} (j x : Fin k) (s : Bool) : (F.lit j s).hit x=(if j=x then 1 else 0) := by
  cases s <;> by_cases e : j=x <;> simp [F.hit,F.occ,e]
lemma hit_gate {k} (a : Bool) (l r : F k) (x : Fin k) : (F.gate a l r).hit x = l.hit x+r.hit x := by
  simp only [F.hit,F.occ]; omega

lemma fg_cap {k} (x : Fin k) (live : Bool) (a : List (F k)) (b : List (Nat × Nat))
    (bounded : ∀ i, (a.getD i (.c false)).hit x ≤ if live then sums (b.getD i (0,0)) else 0) (g : Gate)
    (ok : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    (fg a g).hit x ≤ if live then sums (countG b g) else 0 := by
  obtain ⟨o,is⟩ := g; rcases ok with ⟨ok,sz⟩; rcases ok with rfl|rfl|rfl <;>
    cases is with
    | nil => simp [fg,F.flip,hit_c]
    | cons i is =>
      have hi := bounded i
      cases is with
      | nil => cases live <;> simp [fg,countG,hit_c,hit_flip,sums,List.getD_eq_getElem?_getD] at hi ⊢ <;> omega
      | cons j rest =>
        have e : rest=[] := by simpa using sz
        subst rest; have hj := bounded j
        cases live <;> simp [fg,countG,hit_gate,hit_flip,sums,List.getD_eq_getElem?_getD] at hi hj ⊢ <;> omega

def initF (A B : Finset (Fin k)) := List.ofFn (seed A B) ++ [.c false,.c true]
def form (A B : Finset (Fin k)) (D : Circuit) := (D.gates.foldl (fun w g => w ++ [fg w g]) (initF A B)).getD D.output (.c false)
noncomputable def clock (k : Nat) (D : Circuit) := (D.gates.foldl (fun ts g => ts ++ [timeG ts g]) (List.replicate (k+2) 0)).getD D.output 0

lemma point_bound (A B : Finset (Fin k)) (D : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo D) (x : Fin k) :
    (form A B D).hit x ≤ if x∈B \ A then sums (cnt {x} D) else 0 := by
  let live := decide (x∈B \ A)
  have cap := parallelFold (R := fun (f : F k) c => f.hit x ≤ if live then sums c else 0) (.c false) (0,0) (Nat.zero_le _) fg countG _ (fg_cap x live) _ fan (initF A B) (cs {x}) (by simp [initF,cs]) (by
    intro j; by_cases h : j<k
    · let i : Fin k := ⟨j,h⟩
      by_cases eq : i=x
      · subst x
        simp [initF,cs,seed,i,live,sums,List.getD_eq_getElem?_getD,List.getElem?_append,h,hit_lit,hit_c] <;> split_ifs <;> simp_all [hit_c,hit_lit]
      · have neq : (⟨j,h⟩ : Fin k)≠x := eq
        simp [initF,cs,seed,sums,List.getD_eq_getElem?_getD,List.getElem?_append,h,neq] <;> split_ifs <;> simp_all [hit_lit,hit_c]
    · have zero : (([F.c false,F.c true] : List (F k)).getD (j-k) (.c false)).hit x=0 := by rcases (j-k) with _|(_|l) <;> rfl
      simp [initF,List.getD_eq_getElem?_getD,List.getElem?_append,h] at zero ⊢; simp [zero]) D.output
  simpa only [live,decide_eq_true_eq,form,cnt] using cap

lemma cost_count (A B : Finset (Fin k)) (D : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo D) : (form A B D).cost ≤ sums (cnt (B \ A) D) := by
  let init := List.ofFn (seed A B) ++ [.c false,.c true]
  let f := (D.gates.foldl (fun w g => w ++ [fg w g]) init).getD D.output (.c false)
  have tm : f.cost ≤ sums (cnt (B \ A) D) := parallelFold (R := fun (f : F k) c => f.cost ≤ sums c) (.c false) (0,0) (Nat.zero_le _) fg countG _ fg_count _ fan init (cs (B \ A)) (by simp [init,cs]) (by
    intro i; by_cases hi : i<k
    · simp [init,cs,sums,List.getD_eq_getElem?_getD,List.getElem?_append,hi,seed]; split_ifs <;> simp_all [F.cost]
    · have h : (([F.c false,F.c true] : List (F k)).getD (i-k) (.c false)).cost = 0 := by rcases (i-k) with _|(_|l) <;> rfl
      simp [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi] at h ⊢; simp [h]) D.output
  exact tm

lemma cost_time (A B : Finset (Fin k)) (D : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo D) : (form A B D).cost ≤ 2^(clock k D) := by
  let init := List.ofFn (seed A B) ++ [.c false,.c true]
  let f := (D.gates.foldl (fun w g => w ++ [fg w g]) init).getD D.output (.c false)
  have tm : f.cost ≤ _ := parallelFold (R := fun (f : F k) t => f.cost ≤ 2^t) (.c false) 0 (Nat.zero_le _) fg timeG _ fg_time _ fan init (List.replicate (k+2) 0) (by simp [init]) (by
    intro i; by_cases hi : i<k
    · simp [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi,seed]; split <;> first | split <;> simp [F.cost] | simp [F.cost]
    · have h : (([F.c false,F.c true] : List (F k)).getD (i-k) (.c false)).cost = 0 := by rcases (i-k) with _|(_|l) <;> rfl
      simp [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi] at h ⊢; simp [h]) D.output
  exact tm

lemma form_safe {k} (A B : Finset (Fin k)) (D : Circuit) (p q : Nat)
    (hAB : A ⊆ B) (fan : PEqualNP.MetaComplexity.FanInTwo D)
    (safe : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < p → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=false) ∧
       ((B \ Y).card < q → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=true))) :
    Safe (B \ A) (form A B D) p q := by
  let init := List.ofFn (seed A B) ++ [.c false,.c true]
  let f := (D.gates.foldl (fun w g => w ++ [fg w g]) init).getD D.output (.c false)
  change Safe (B \ A) f p q
  intro x
  let Y := ys A B x
  have sub : A ⊆ Y := Finset.subset_union_left
  have sub' : Y ⊆ B := Finset.union_subset hAB ((Finset.filter_subset ..).trans Finset.sdiff_subset)
  have eq : f.val x = D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true]) := by
    apply parallelFold (R := fun (f : F k) b => f.val x=b) (.c false) false rfl fg bg _ (fg_eval x) _ fan init _ (by simp [init]) _ D.output
    intro i; by_cases hi : i<k
    · simp [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi,Y,ys,seed]; split <;> first | split <;> simp_all [F.val] | simp_all [F.val]
    · have h : (([F.c false,F.c true] : List (F k)).getD (i-k) (.c false)).val x = [false,true].getD (i-k) false := by rcases (i-k) with _|(_|l) <;> rfl
      simpa [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi] using h
  have h1 : Y \ A = (B \ A).filter (fun i => x i=true) := by ext i; simp [Y,ys]; tauto
  have h2 : B \ Y = (B \ A).filter (fun i => x i=false) := by ext i; cases e : x i <;> simp [Y,ys,e] <;> tauto
  have h := safe Y sub sub'
  unfold weight; rw [← h1,← h2,eq]; constructor <;> intro ev <;> by_contra! contra
  · simp [ev] at h; omega
  · simp [ev] at h; omega


lemma charges (A B : Finset (Fin k)) (D : Circuit) (p q : Nat)
    (hAB : A ⊆ B) (fan : PEqualNP.MetaComplexity.FanInTwo D) (big : 3≤min p q)
    (safe : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < p → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=false) ∧
       ((B \ Y).card < q → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=true))) :
    let H := B \ A
    let fee := (min p q-2)*(H.sum (fun j => sums (cnt {j} D)-1))
    2*(p*q - sums (cnt H D)) ≤ fee ∧ 2*(p*q-2^clock k D) ≤ fee := by
  intro H fee
  let f := form A B D
  have t := weighted H H f p q (min p q-2) (fun j => sums (cnt {j} D)) (by omega) (form_safe A B D p q hAB fan safe)
    (by intro i hi; have h := point_bound A B D fan i; simpa [f,H,hi,show i∉B \ A from hi] using h)
    (by intro i; exact (point_bound A B D fan i).trans (by split <;> simp))
  have lo : f.cost≤sums (cnt H D) := cost_count A B D fan
  have dep : f.cost≤2^clock k D := cost_time A B D fan
  dsimp only [fee]; omega

end PEqualNP.Outside.L_lib_1474.Sign

theorem PEqualNP.Outside.L_lib_1474 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let delay := fun (k c e : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let times := D.gates.foldl (fun (ts : List Nat) g =>
    let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
    ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
      else mx+(if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then c else e)]) (List.replicate (k+2) 0)
  times.getD D.output 0
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
∀ (n k : Nat) (X : Fin (n+1) → Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit)
  (tap p q d : Fin n → Nat) (S : Finset (Fin n)) (c : Fin k → Nat),
  let E := fun i : Fin n => { D with output := tap i }
  let H := fun i : Fin n => X i.succ \ X i.castSucc
  let m := fun i : Fin n => min (p i) (q i)
  let hits := fun (i : Fin n) (j : Fin k) =>
    let z := occ {j} (E i)
    z.1+z.2
  let need := fun i : Fin n => (2*((p i)*(q i)-2^(d i))+(m i-3))/(m i-2)
  (∀ i : Fin n, X i.castSucc ⊆ X i.succ) →
  (∀ i ∈ S, 3 ≤ m i ∧ valid k (E i) ∧ protects (E i) (X i.castSucc) (X i.succ) (p i) (q i) ∧
    delay k 1 1 (E i) ≤ d i ∧ ∀ j ∈ H i, hits i j ≤ 1+c j) →
  (∀ i ∈ S,
    let z := occ (H i) (E i)
    let L := z.1+z.2
    2*((p i)*(q i)-L) ≤ (m i-2)*((H i).sum (fun j => hits i j-1))) ∧
  ∀ T : Finset (Fin n), T ⊆ S → T.sum need ≤ (T.biUnion H).sum c) := by
  intro valid run delay occ protects n k X D tap p q d S c E H m hits need chain allFit
  have actual (J : Finset (Fin k)) (V : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.Outside.L_lib_1474.Sign.cnt J V=occ J V := by
    dsimp only [PEqualNP.Outside.L_lib_1474.Sign.cnt,occ,PEqualNP.Outside.L_lib_1474.Sign.cs]; congr 4; funext j; by_cases h : j∈J <;> simp [h]
  have both (i : Fin n) (hi : i∈S) :
      let z := occ (H i) (E i)
      let fee := (m i-2)*((H i).sum (fun j => hits i j-1))
      2*(p i*q i-(z.1+z.2)) ≤ fee ∧ 2*(p i*q i-2^d i) ≤ fee := by
    obtain ⟨big,ok,safe,depth,_⟩ := allFit i hi
    have bound := PEqualNP.Outside.L_lib_1474.Sign.charges (X i.castSucc) (X i.succ) (E i) (p i) (q i) (chain i) ok.1 big (by
      intro Y h1 h2
      have hy := safe Y h1 h2
      convert! hy using 1 <;> congr! 20 <;> simp only [run,PEqualNP.CircuitLowerBounds.Circuit.eval] <;> congr 4 <;> funext j <;> exact decide_eq_decide.mpr Iff.rfl)
    have eqH : H i = X i.succ \ X i.castSucc := by ext j; simp [H]
    dsimp only at bound ⊢
    rw [← eqH] at bound
    simp only [actual,PEqualNP.Outside.L_lib_1474.Sign.sums] at bound
    have time : PEqualNP.Outside.L_lib_1474.Sign.clock k (E i) ≤ d i := depth
    have pow := Nat.pow_le_pow_right (n := 2) (by decide) time
    constructor
    · exact bound.1
    · apply le_trans _ bound.2
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left pow _)
  constructor
  · intro i hi; exact (both i hi).1
  · intro T hTS
    letI : DecidableEq (Fin k) := fun a b => Classical.propDecidable (a=b)
    have mono : Monotone X := Fin.monotone_iff_le_succ.mpr chain
    have apart {i j : Fin n} (lt : i < j) : Disjoint (H i) (H j) := by
      apply Finset.disjoint_left.mpr; intro x hxi hxj
      have mem (a) : x∈H a ↔ x∈X a.succ ∧ x∉X a.castSucc := Finset.mem_sdiff
      exact (mem j |>.mp hxj).2 (mono (show i.succ ≤ j.castSucc from lt) ((mem i).mp hxi).1)
    have disj : Set.PairwiseDisjoint (↑T) H := by
      intro i _ j _ ne; rcases lt_or_gt_of_ne ne with lt|lt; exact apart lt; exact (apart lt).symm
    rw [Finset.sum_biUnion disj]
    apply Finset.sum_le_sum; intro i hi
    have fit := allFit i (hTS hi)
    have budget : (H i).sum (fun j => hits i j-1) ≤ (H i).sum c := by
      apply Finset.sum_le_sum; intro j hj; have := fit.2.2.2.2 j hj; omega
    have h := (both i (hTS hi)).2.trans (Nat.mul_le_mul_left _ budget)
    have hm := fit.1
    change (2*(p i*q i-2^d i)+(m i-3))/(m i-2) ≤ (H i).sum c
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < m i-2)).mpr
    rw [Nat.succ_mul ((H i).sum c) (m i-2),Nat.mul_comm ((H i).sum c) (m i-2)]; omega
