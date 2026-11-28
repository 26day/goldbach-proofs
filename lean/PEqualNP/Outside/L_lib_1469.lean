import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1469.Sign

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

private theorem edit_cost {k} (f : F k) (j : Fin k) (b v : Bool) :
    (f.edit j b v).cost + f.occ j b = f.cost := by
  induction f with
  | c => rfl
  | lit => simp only [F.edit,F.occ]; split <;> simp [F.cost]
  | gate a l r hl hr => simp only [F.cost,F.edit,F.occ]; omega

private theorem edit_none {k} (f : F k) (j : Fin k) (b v : Bool) (zero : f.occ j b=0) :
    f.edit j b v = f := by
  induction f with
  | c => rfl
  | lit => simp only [F.edit,F.occ] at *; split at * <;> simp_all
  | gate a l r hl hr => simp only [F.occ,Nat.add_eq_zero_iff] at zero; simp [F.edit,hl zero.1,hr zero.2]

private theorem literal_set {k} (j : Fin k) (x : Fin k → Bool) (b v : Bool) (f : F k)
    (h : f.occ j (!b) = 0) : (f.edit j b v).val x = f.val (Function.update x j (v == b)) := by
  induction f with
  | c => rfl
  | lit i s =>
    by_cases hj : i=j
    · subst i; cases b <;> cases v <;> cases s <;> simp_all [F.edit,F.val,F.occ]
    · simp [F.edit,F.val,hj,Function.update_of_ne hj]
  | gate a l r hl hr => simp only [F.occ,Nat.add_eq_zero_iff] at h; simp [F.edit,F.val,hl h.1,hr h.2]

private theorem unchanged {k} (j : Fin k) (x : Fin k → Bool) (b : Bool) (f : F k)
    (hp : f.occ j true = 0) (hn : f.occ j false = 0) :
    f.val (Function.update x j b) = f.val x := by
  simpa [edit_none f j true b hp] using (literal_set j x true b f hn).symm

private theorem edit_same {k} (f : F k) (j : Fin k) (x : Fin k → Bool) (b : Bool) :
    (f.edit j b (x j == b)).val x = f.val x := by
  induction f with
  | c => rfl
  | lit i s => by_cases h : i=j ∧ s=b <;> simp only [F.edit,if_pos,if_neg,h,F.val] <;> simp_all <;> rfl
  | gate a l r hl hr => simp [F.edit,F.val,hl,hr]

private theorem eval_mono (a : Bool) {l r l' r' : Bool} (hl : l ≤ l') (hr : r ≤ r') : op a l r ≤ op a l' r' := by
  revert hl hr; cases a <;> cases l <;> cases r <;> cases l' <;> cases r' <;> decide

private theorem edit_le {k} (f : F k) (j : Fin k) (x : Fin k → Bool) (b : Bool) :
    (f.edit j b false).val x ≤ f.val x ∧ f.val x ≤ (f.edit j b true).val x := by
  induction f with
  | c => exact ⟨le_rfl,le_rfl⟩
  | lit i s => by_cases h : i=j ∧ s=b <;> simp [F.edit,F.val,h]
  | gate a l r hl hr => exact ⟨eval_mono a hl.1 hr.1,eval_mono a hl.2 hr.2⟩

private def Witness {k} (f : F k) (j : Fin k) (v : Bool) := ∀ x,
    (f.edit j false v).val x = f.val x ∨
    (f.edit j false v).val x = f.val (Function.update x j (!v))

private theorem mixed_binary (a l r t u w : Bool) (bound : if a then w ≤ op a l r else op a l r ≤ w)
    (mix : w = op a t r ∨ w = op a l u) : w = op a l r ∨ w = op a t u := by
  revert bound mix; cases a <;> cases l <;> cases r <;> cases t <;> cases u <;> cases w <;> decide

private theorem split_edit {k} (l r : F k) (j : Fin k) (a : Bool)
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

private theorem sparse_edit {k} (f : F k) (j : Fin k) (hp : f.occ j true ≤ 1) (hn : f.occ j false ≤ 1) :
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

private def weight {k} (H : Finset (Fin k)) (x : Fin k → Bool) (b : Bool) := (H.filter (fun i => x i = b)).card
private def Safe {k} (H : Finset (Fin k)) (f : F k) (p q : Nat) := ∀ x,
    (f.val x = true → p ≤ weight H x true) ∧ (f.val x = false → q ≤ weight H x false)

private theorem weight_update {k} (H : Finset (Fin k)) (x : Fin k → Bool) (j : Fin k) (b : Bool) :
    weight H (Function.update x j b) (!b) ≤ weight H x (!b) ∧
    weight H (Function.update x j b) b ≤ weight H x b + 1 := by
  constructor
  · apply Finset.card_le_card; intro i hi; simp only [Finset.mem_filter] at *; by_cases eq : i=j <;> simp_all [Function.update_of_ne]
  · apply le_trans (b := (insert j (H.filter (fun i => x i = b))).card)
    · apply Finset.card_le_card; intro i hi; by_cases eq : i=j <;> simp_all [Function.update_of_ne]
    · exact Finset.card_insert_le ..

private theorem safe_edit {k} {H : Finset (Fin k)} {f : F k} {j : Fin k} {p q : Nat} {v : Bool}
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

private theorem other_occ {k} (f : F k) (j : Fin k) (v b : Bool) :
    (f.edit j b v).occ j (!b) = f.occ j (!b) := by
  induction f with
  | c => rfl
  | lit i s => by_cases h : i=j ∧ s=b <;> simp [F.edit,h,F.occ] <;> rcases h with ⟨rfl,rfl⟩ <;> cases b <;> rfl
  | gate a l r hl hr => simp [F.edit,F.occ,hl,hr]

private theorem eval_fixed {k} (f : F k) (j : Fin k) (v : Bool) (x : Fin k → Bool) :
    ((f.edit j true v).edit j false (!v)).val x = f.val (Function.update x j v) := by
  induction f with
  | c => rfl
  | lit i s => by_cases eq : i=j <;> cases s <;> simp [F.edit,F.val,eq,Function.update_of_ne]
  | gate a l r hl hr => simp [F.edit,F.val,hl,hr]

private def Forces {k} (f : F k) (b : Bool) (s : Finset (Fin k)) := ∀ x : Fin k → Bool, (∀ i ∈ s, x i=b) → f.val x=b
private def Cert {k} (f : F k) := ∃ S T : Finset (Fin k), Forces f true S ∧ Forces f false T ∧ S.card*T.card ≤ f.cost
private theorem combine {k} {l r : F k} (a : Bool) (hl : Cert l) (hr : Cert r) : Cert (.gate a l r) := by
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

private def Clean {k} (f : F k) := (∃ b, ∀ x, f.val x=b) ∨ Cert f
private theorem transport {k} {f g : F k} (h : ∀ x, f.val x=g.val x) (le : g.cost≤f.cost) : Clean g → Clean f := by
  rintro (⟨b,hb⟩|⟨S,T,s,t,c⟩)
  · exact Or.inl ⟨b,fun x => (h x).trans (hb x)⟩
  · exact Or.inr ⟨S,T,fun x hx => (h x).trans (s x hx),fun x hx => (h x).trans (t x hx),c.trans le⟩
private theorem clean_gate {k} (a : Bool) (l r : F k) (hl : Clean l) (hr : Clean r) : Clean (.gate a l r) := by
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
private theorem clean_positive {k} (f : F k) (pos : ∀ j, f.occ j false=0) : Clean f := by
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

private theorem clean_bound {k} (H : Finset (Fin k)) (f : F k) (p q : Nat) (safe : Safe H f p q) (c : Clean f) : p*q≤f.cost := by
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

private theorem signed_bound {k} (H : Finset (Fin k)) (f : F k) (p q : Nat)
    (sm : min p q ≤ 3) (safe : Safe H f p q) : p*q ≤ f.cost := by
  by_cases neg : ∃ j, f.occ j false ≠ 0
  · obtain ⟨j, hj⟩ := neg
    by_cases heavy : 3 ≤ f.occ j true + f.occ j false
    · let v := decide (q ≤ p)
      let g := (f.edit j true v).edit j false (!v)
      have cc : g.cost + f.occ j true + f.occ j false = f.cost := by
        have a := edit_cost f j true v
        have b := edit_cost (f.edit j true v) j false (!v)
        have c := other_occ f j v true
        simp only [Bool.not_true] at c
        rw [c] at b
        dsimp only [g]; omega
      have dec : g.cost < f.cost := by omega
      by_cases cmp : q ≤ p
      · have veq : v=true := by simp [v,cmp]
        have hs : Safe H g (p-1) q := by
          intro x; have s := safe (Function.update x j true); have wt := weight_update H x j true
          simp only [g,eval_fixed,veq]; exact ⟨fun h => by have := s.1 h; omega,fun h => (s.2 h).trans wt.1⟩
        have ih := signed_bound H g (p-1) q (by omega) hs
        cases p with
        | zero => simp
        | succ p => simp only [Nat.succ_sub_one] at ih; rw [Nat.succ_mul]; omega
      · have veq : v=false := by simp [v,cmp]
        have hs : Safe H g p (q-1) := by
          intro x; have s := safe (Function.update x j false); have wt := weight_update H x j false
          simp only [g,eval_fixed,veq]; exact ⟨fun h => (s.1 h).trans wt.1,fun h => by have := s.2 h; omega⟩
        have ih := signed_bound H g p (q-1) (by omega) hs
        cases q with
        | zero => simp
        | succ q => simp only [Nat.succ_sub_one] at ih; rw [Nat.mul_succ]; omega
    · have ex : ∃ v, Witness f j v := by
        by_cases nonePos : f.occ j true=0
        · exact ⟨true,fun x => Or.inr (literal_set j x false true f nonePos)⟩
        · exact sparse_edit f j (by omega) (by omega)
      obtain ⟨v,hv⟩ := ex
      have c := edit_cost f j false v
      have dec : (f.edit j false v).cost < f.cost := by omega
      exact (signed_bound H (f.edit j false v) p q sm (safe_edit safe hv)).trans dec.le
  · exact clean_bound H f p q safe (clean_positive f (by simpa using neg))
termination_by f.cost

end PEqualNP.Outside.L_lib_1469.Sign


namespace PEqualNP.Outside.L_lib_1469
open PEqualNP.CircuitLowerBounds

private theorem parallelFold {α β} {R : α → β → Prop} (d : α) (e : β) (de : R d e)
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
private noncomputable def countG (zs : List (Nat × Nat)) (g : Gate) :=
  let ab := g.inputs.foldl (fun (acc : Nat × Nat) j => let z := zs.getD j (0,0); (acc.1+z.1,acc.2+z.2)) (0,0)
  let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
  if g.op=.not then (h.2,h.1) else ab
end PEqualNP.Outside.L_lib_1469
namespace PEqualNP.Outside.L_lib_1469.Sign
open PEqualNP.CircuitLowerBounds

def F.flip {k} : F k → F k
  | .c b => .c (!b)
  | .lit j s => .lit j (!s)
  | .gate a l r => .gate (!a) l.flip r.flip
private theorem flip_cost {k} (f : F k) : f.flip.cost = f.cost := by induction f <;> simp_all [F.cost,F.flip]
private theorem flip_val {k} (f : F k) (x : Fin k → Bool) : f.flip.val x = !(f.val x) := by
  induction f with
  | c => rfl
  | lit i s => cases s <;> cases h : x i <;> simp [F.flip,F.val,h]
  | gate a l r il ir => cases a <;> simp [F.flip,F.val,op,il,ir]
private def fg {k} (w : List (F k)) (g : Gate) : F k :=
  let atI := fun i => w.getD i (.c false)
  let comb := fun a => match g.inputs with
    | [] => .c a | [i] => atI i | i::j::_ => .gate a (atI i) (atI j)
  match g.op with
  | .not => ((g.inputs.head?.map atI).getD (.c false)).flip
  | .and => comb true | _ => comb false
private def bg (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem fg_eval {k} (x : Fin k → Bool) (a : List (F k)) (b : List Bool)
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

private def sums (c : Nat × Nat) := c.1+c.2
private def cs {k} (H : Finset (Fin k)) := List.ofFn (fun j : Fin k => ((if j∈H then 1 else 0,0) : Nat × Nat)) ++ [(0,0),(0,0)]
private noncomputable def cnt {k} (H : Finset (Fin k)) (D : Circuit) := (D.gates.foldl (fun zs g => zs ++ [countG zs g]) (cs H)).getD D.output (0,0)

private theorem fg_count {k} (a : List (F k)) (b : List (Nat × Nat))
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
private def seed {k} (A B : Finset (Fin k)) (j : Fin k) : F k := if j∈A then .c true else if j∈B then .lit j true else .c false
private def ys {k} (A B : Finset (Fin k)) (x : Fin k → Bool) := A ∪ ((B \ A).filter (fun i => x i = true))
private theorem product_count {k} (A B : Finset (Fin k)) (D : Circuit) (p q : Nat)
    (hAB : A ⊆ B) (sm : min p q ≤ 3) (fan : PEqualNP.MetaComplexity.FanInTwo D)
    (safe : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B →
      (((Y \ A).card < p → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=false) ∧
       ((B \ Y).card < q → D.eval (List.ofFn (fun j => decide (j∈Y)) ++ [false,true])=true))) :
    p*q ≤ sums (cnt (B \ A) D) := by
  let init := List.ofFn (seed A B) ++ [.c false,.c true]
  let f := (D.gates.foldl (fun w g => w ++ [fg w g]) init).getD D.output (.c false)
  have tm : f.cost ≤ sums (cnt (B \ A) D) := parallelFold (R := fun (f : F k) c => f.cost ≤ sums c) (.c false) (0,0) (Nat.zero_le _) fg countG _ fg_count _ fan init (cs (B \ A)) (by simp [init,cs]) (by
    intro i; by_cases hi : i<k
    · simp [init,cs,sums,List.getD_eq_getElem?_getD,List.getElem?_append,hi,seed]; split_ifs <;> simp_all [F.cost]
    · have h : (([F.c false,F.c true] : List (F k)).getD (i-k) (.c false)).cost = 0 := by rcases (i-k) with _|(_|l) <;> rfl
      simp [init,List.getD_eq_getElem?_getD,List.getElem?_append,hi] at h ⊢; simp [h]) D.output
  apply le_trans _ tm
  apply signed_bound (B \ A) f p q sm
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

private abbrev Mk (k : Nat) := (Finset (Fin k) × Finset (Fin k)) × (Finset (Fin k) × Finset (Fin k))
private def mz {k} : Mk k := ((∅,∅),(∅,∅))
private noncomputable def mg {k} [DecidableEq (Fin k)] (ts : List (Mk k)) (g : Gate) : Mk k :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let a := (g.inputs.head?.map (fun j => ts.getD j mz)).getD mz
  let b := (g.inputs[1]?.map (fun j => ts.getD j mz)).getD mz
  let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
  let u := a.2.1 ∪ b.2.1
  let v := a.2.2 ∪ b.2.2
  if g.op=.not then ((a.1.2,a.1.1),(a.2.2,a.2.1))
  else ((a.1.1 ∪ b.1.1,a.1.2 ∪ b.1.2),if g.op=.and then (u ∪ cross,v) else (u,v ∪ cross))
private def ms {k} := List.ofFn (fun j : Fin k => ((({j},∅),(∅,∅)) : Mk k)) ++ [mz,mz]
private noncomputable def mark {k} (D : Circuit) := (D.gates.foldl (fun ts g => ts ++ [mg ts g]) (@ms k)).getD D.output mz
private theorem cutUnion {k} [DecidableEq (Fin k)] (H A B : Finset (Fin k)) : (H ∩ (A ∪ B)).card ≤ (H ∩ A).card+(H ∩ B).card := by
  rw [Finset.inter_union_distrib_left]; exact Finset.card_union_le ..
set_option maxHeartbeats 2400000 in
private theorem mark_count {k} (H : Finset (Fin k)) (D : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo D) :
    let t := mark (k := k) D
    (H ∩ (t.1.1 ∪ t.1.2)).card ≤ sums (cnt H D) := by
  letI : DecidableEq (Fin k) := fun i j => Classical.propDecidable (i=j)
  let rel := fun (t : Mk k) (c : Nat × Nat) => (H ∩ t.1.1).card ≤ c.1 ∧ (H ∩ t.1.2).card ≤ c.2
  have work := parallelFold (R := rel) mz (0,0) (by simp [rel,mz]) mg countG (fun g => g.inputs.length≤2) (by
    intro a b eq g sz
    obtain ⟨o,is⟩ := g
    cases is with
    | nil => by_cases hn : o=.not <;> simp [rel,mg,countG,mz,hn]
    | cons i is =>
      have hi := eq i
      cases is with
      | nil => by_cases hn : o=.not <;> simp [rel,mg,countG,mz,hn] <;> simp only [rel,List.getD_eq_getElem?_getD] at hi <;> first | exact hi | exact ⟨hi.2,hi.1⟩
      | cons j rest =>
        have e : rest=[] := by simpa using sz
        subst rest; have hj := eq j
        by_cases hn : o=.not
        · simp [rel,mg,countG,hn]; simp only [rel,List.getD_eq_getElem?_getD] at hi; exact ⟨hi.2,hi.1⟩
        · have u := cutUnion H (a.getD i mz).1.1 (a.getD j mz).1.1
          have v := cutUnion H (a.getD i mz).1.2 (a.getD j mz).1.2
          simp [rel,mg,countG,hn] <;> simp only [rel,List.getD_eq_getElem?_getD] at hi hj u v <;> exact ⟨u.trans (Nat.add_le_add hi.1 hj.1),v.trans (Nat.add_le_add hi.2 hj.2)⟩) D.gates (fun g hg => (fan g hg).2) ms (cs H) (by simp [ms,cs]) (by
    intro i; by_cases hi : i<k
    · simp [ms,cs,rel,List.getD_eq_getElem?_getD,List.getElem?_append,hi]; split <;> simp_all
    · have ha : ([mz,mz] : List (Mk k)).getD (i-k) mz = mz := by rcases (i-k) with _|(_|l) <;> rfl
      have hb : ([(0,0),(0,0)] : List (Nat × Nat)).getD (i-k) (0,0) = (0,0) := by rcases (i-k) with _|(_|l) <;> rfl
      simp [rel,ms,cs,List.getD_eq_getElem?_getD,List.getElem?_append,hi] at ha hb ⊢; rw [ha,hb]; simp [mz]) D.output
  let t := mark (k := k) D
  have h : rel t (cnt H D) := work
  have u := cutUnion H t.1.1 t.1.2
  convert! u.trans (Nat.add_le_add h.1 h.2) using 1 <;> congr! 10

end PEqualNP.Outside.L_lib_1469.Sign

theorem PEqualNP.Outside.L_lib_1469 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
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
let marks := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let V := Finset (Fin k)
  let Z : (V × V) × (V × V) := ((∅,∅),(∅,∅))
  let xs := List.ofFn (fun j : Fin k => ((({j},∅),(∅,∅)) : (V × V) × (V × V))) ++ [Z,Z]
  let ws := D.gates.foldl (fun (ts : List ((V × V) × (V × V))) g =>
    let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
    let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
    let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
    let u := a.2.1 ∪ b.2.1
    let v := a.2.2 ∪ b.2.2
    ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((a.1.2,a.1.1),(a.2.2,a.2.1))
      else ((a.1.1 ∪ b.1.1,a.1.2 ∪ b.1.2),
        if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (u ∪ cross,v) else (u,v ∪ cross))]) xs
  ws.getD D.output Z
∀ (k p q : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset (Fin k)),
  min p q=3 → valid k D → A ⊆ B → protects D A B p q →
  let H := B \ A
  let s := marks k D
  let u := (H ∩ (s.1.1 ∪ s.1.2)).card
  let b := (H ∩ (s.2.1 ∩ s.2.2)).card
  let L := (occ H D).1+(occ H D).2
  p*q ≤ L+b ∧ 2*(p*q)+u ≤ 3*L ∧ 3*(p*q) ≤ 4*L) := by
  intro valid run occ protects marks k p q D A B hmin hfit hab hs H s u b L
  have t := PEqualNP.Outside.L_lib_1469.Sign.product_count A B D p q hab hmin.le hfit.1 (by
    intro Y h1 h2
    have hy := hs Y h1 h2
    convert! hy using 1 <;> congr! 20 <;> simp only [run,PEqualNP.CircuitLowerBounds.Circuit.eval] <;> congr 4 <;> funext j <;> exact decide_eq_decide.mpr Iff.rfl)
  have cm := PEqualNP.Outside.L_lib_1469.Sign.mark_count H D hfit.1
  have eqH : H = B \ A := by ext i; simp [H]
  rw [← eqH] at t
  have eqC : PEqualNP.Outside.L_lib_1469.Sign.cnt H D = occ H D := by
    dsimp only [PEqualNP.Outside.L_lib_1469.Sign.cnt,occ,PEqualNP.Outside.L_lib_1469.Sign.cs]; congr 4; funext j; by_cases h : j ∈ H <;> simp [h]
  have eqS : PEqualNP.Outside.L_lib_1469.Sign.mark (k := k) D = s := by rfl
  dsimp only [PEqualNP.Outside.L_lib_1469.Sign.sums] at cm t
  rw [eqC] at cm t
  rw [eqS] at cm
  have hu : u ≤ L := by convert! cm using 1 <;> congr! 10
  change p*q ≤ L at t
  omega
