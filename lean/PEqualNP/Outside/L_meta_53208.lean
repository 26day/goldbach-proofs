import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_meta_53208

open Classical PEqualNP GraphInversionSeeds GraphSampleDistance

def oneColor (_ : Fin n) : Fin 1 := 0

def connected (E : Finset (Edge n)) := ∀ Z : W n,
  (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ

def validBank (E : Finset (Edge n)) (D : Nat) (w : W n → Nat) :=
  ∀ lost : W n → Nat, (∑ x, lost x) < D →
    keeps (Finset.univ.filter (fun x => lost x < w x)) E oneColor

def allMargins (E : Finset (Edge n)) (D : Nat) (w : W n → Nat) :=
  (∀ f ∈ target E, ∀ g ∈ target E, f ≠ g → D ≤ margin Finset.univ w f g) ∧
  ∀ f ∈ target E, ∀ g ∈ raw E, D ≤ margin Finset.univ w f g

lemma localCriterion (n : Nat) (hn : 2 ≤ n) (E : Finset (Edge n))
    (sorted : ∀ e ∈ E, e.1 < e.2) (conn : connected E) (A : Finset (W n)) :
    keeps A E oneColor ↔ (∅ ∈ A ∧ Finset.univ ∈ A) ∧ separates A E := by
  classical
  have onto : Function.Surjective (oneColor (n := n)) :=
    fun _ => ⟨⟨0, by omega⟩, Subsingleton.elim ..⟩
  have part : GraphPriceCalibration.classes E oneColor := by
    intro V
    constructor
    · intro h i k _
      rcases conn V h with rfl | rfl <;> simp
    · intro h e _
      exact h e.1 e.2 rfl
  have equiv := GraphSampleDistance.criterion n 1 E oneColor onto sorted part A
    (fun _ => 1) 0 (by simp)
  change (∀ lost : W n → Nat, A.sum lost ≤ 0 →
      keeps (A.filter (fun u => lost u < 1)) E oneColor) ↔
    (∀ j : Fin 1, 0 < (lows A (GraphSeedSamples.block oneColor j)).sum
      (fun _ => min 1 1)) ∧
    (∀ f ∈ target E, ∀ g ∈ target E, f ≠ g →
      0 < margin A (fun _ => 1) f g) ∧
    ∀ f ∈ target E, ∀ g ∈ raw E, 0 < margin A (fun _ => 1) f g at equiv
  have lhs : (∀ lost : W n → Nat, A.sum lost ≤ 0 →
      keeps (A.filter (fun u => lost u < 1)) E oneColor) ↔ keeps A E oneColor := by
    constructor
    · intro h
      simpa using h (fun _ => 0) (by simp)
    · intro h lost hl
      have : ∀ u ∈ A, lost u < 1 := by
        intro u hu
        have := Finset.single_le_sum (f := lost) (fun _ _ => Nat.zero_le _) hu
        exact Nat.lt_succ_of_le (this.trans hl)
      simpa only [Finset.filter_true_of_mem this] using h
  have blockEq (j : Fin 1) : GraphSeedSamples.block (oneColor (n := n)) j = Finset.univ := by
    simp [GraphSeedSamples.block, oneColor, Subsingleton.elim j 0]
  rw [←lhs, equiv]
  have du (u : W n) : Disjoint u Finset.univ ↔ u = ∅ := disjoint_top
  have uu (u : W n) : u ∪ Finset.univ = Finset.univ := sup_top_eq u
  simp only [blockEq, lows, du, uu, min_self,
    Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_pos,
    Finset.filter_nonempty_iff, margin, separates, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨h, rest⟩
    obtain ⟨u, hu, rfl, hall⟩ := h 0
    exact ⟨⟨hu,hall⟩,rest⟩
  · rintro ⟨⟨h0,ha⟩,rest⟩
    exact ⟨fun _ => ⟨∅,h0,rfl,ha⟩,rest⟩

lemma robustWitness {α : Type} [Fintype α] [DecidableEq α] (D : Nat) (w : α → Nat)
    (P : α → Prop) [DecidablePred P] :
    (∀ lost : α → Nat, (∑ x, lost x) < D → ∃ u, lost u < w u ∧ P u) ↔
    D ≤ (Finset.univ.filter P).sum w := by
  constructor
  · intro h
    by_contra! bad
    rw [Finset.sum_filter] at bad
    obtain ⟨u, hu, hp⟩ := h (fun x => if P x then w x else 0) bad
    simp [hp] at hu
  · intro large lost cheap
    by_contra! fail
    have bounded : (Finset.univ.filter P).sum w ≤ (Finset.univ.filter P).sum lost := by
      apply Finset.sum_le_sum
      intro u hu
      specialize fail u
      by_contra! bad
      exact fail bad (Finset.mem_filter.mp hu).2
    have := bounded.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    omega

lemma bankIff (n : Nat) (hn : 2 ≤ n) (E : Finset (Edge n))
    (sorted : ∀ e ∈ E, e.1 < e.2) (conn : connected E) (D : Nat) (w : W n → Nat) :
    validBank E D w ↔ (D ≤ w ∅ ∧ D ≤ w Finset.univ) ∧ allMargins E D w := by
  classical
  have one (z : W n) : (∀ lost : W n → Nat, (∑ x, lost x) < D → lost z < w z) ↔ D ≤ w z := by
    simpa [Finset.sum_filter] using robustWitness D w (fun x => x = z)
  have gap (f g : F n) := robustWitness D w (fun x => asWord f x ≠ asWord g x)
  unfold validBank
  simp only [localCriterion n hn E sorted conn, separates, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    exact ⟨⟨(one _).mp (fun l hl => (h l hl).1.1),(one _).mp (fun l hl => (h l hl).1.2)⟩,
      fun f hf g hg ne => (gap f g).mp (fun l hl => (h l hl).2.1 f hf g hg ne),
      fun f hf g hg => (gap f g).mp (fun l hl => (h l hl).2.2 f hf g hg)⟩
  · rintro ⟨⟨he,hu⟩, ht,hr⟩ l hl
    exact ⟨⟨(one _).mpr he l hl,(one _).mpr hu l hl⟩,
      fun f hf g hg ne => (gap f g).mpr (ht f hf g hg ne) l hl,
      fun f hf g hg => (gap f g).mpr (hr f hf g hg) l hl⟩

def adj (E : Finset (Edge n)) (i j : Fin n) := (i,j) ∈ E ∨ (j,i) ∈ E

def apart (i j : Fin n) (x : W n) := ¬ (i ∈ x ↔ j ∈ x)

noncomputable def distance (w : W n → Nat) (i j : Fin n) :=
  (Finset.univ.filter (apart i j)).sum w

lemma clipped (E : Finset (Edge n)) (D : Nat) (w : W n → Nat) (good : validBank E D w)
    (opt : ∀ u, validBank E D u → (∑ x, w x) ≤ ∑ x, u x) (x : W n) : w x ≤ D := by
  let u (z : W n) := min (w z) D
  have ok : validBank E D u := by
    intro lost hl
    have eq : ∀ z, lost z < u z ↔ lost z < w z := by
      intro z
      have lt := lt_of_le_of_lt (Finset.single_le_sum (s := Finset.univ) (f := lost)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)) hl
      simp [u, lt_min_iff, lt]
    simpa only [eq] using good lost hl
  by_contra! bad
  have less : (∑ z, u z) < ∑ z, w z := Finset.sum_lt_sum
    (fun z _ => min_le_left _ _) ⟨x,Finset.mem_univ _, by simpa [u,bad.le] using bad⟩
  exact (not_le_of_gt less) (opt u ok)

def directed (i j : Fin n) : F n := fun x => x i && !(x j)

lemma directed_mem {E : Finset (Edge n)} {i j : Fin n} (h : adj E i j) :
    directed i j ∈ target E := by
  classical
  rcases h with h|h
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem oz h))
  · have eq : directed i j = zo (j,i) := by funext x; exact Bool.and_comm ..
    rw [eq]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

lemma adj_symm {E : Finset (Edge n)} {i j : Fin n} (h : adj E i j) : adj E j i := h.symm

lemma targetDistance (E : Finset (Edge n)) (sorted : ∀ e ∈ E, e.1 < e.2)
    (D : Nat) (w : W n → Nat) (hm : allMargins E D w) (i j : Fin n) (hij : i ≠ j)
    (path : adj E i j ∨ ∃ v, adj E i v ∧ adj E v j) : 2 * D ≤ distance w i j := by
  classical
  have partition (f g p q : F n) (a : D ≤ margin Finset.univ w f g)
      (b : D ≤ margin Finset.univ w p q)
      (splitCut : ∀ u, (if asWord f u ≠ asWord g u then w u else 0) +
        (if asWord p u ≠ asWord q u then w u else 0) = (if apart i j u then w u else 0)) :
      2 * D ≤ distance w i j := by
    unfold margin at a b
    unfold distance
    simp only [Finset.sum_filter] at *
    rw [←Finset.sum_congr rfl (fun u _ => splitCut u),Finset.sum_add_distrib]
    omega
  rcases path with edge | ⟨v,iv,vj⟩
  · have zero : (fun _ => false) ∈ raw E := by simp [raw]
    apply partition _ _ _ _ (hm.2 _ (directed_mem edge) _ zero)
      (hm.2 _ (directed_mem (adj_symm edge)) _ zero)
    intro u
    by_cases hi : i ∈ u <;> by_cases hj : j ∈ u <;> simp [asWord,directed,apart,hi,hj]
  · have irr (k : Fin n) : ¬ adj E k k := by
      rintro (h|h) <;> exact (lt_irrefl k) (sorted _ h)
    have vi : v ≠ i := by rintro rfl; exact irr _ iv
    have vj' : v ≠ j := by rintro rfl; exact irr _ vj
    have ne1 : directed i v ≠ directed j v := by
      intro eq
      have val := congrFun eq (fun k => decide (k=i))
      simp [directed,hij.symm,vi] at val
    have ne2 : directed v i ≠ directed v j := by
      intro eq
      have val := congrFun eq (fun k => decide (k≠i))
      simp [directed,hij.symm,vi] at val
    apply partition _ _ _ _ (hm.1 _ (directed_mem iv) _ (directed_mem (adj_symm vj)) ne1)
      (hm.1 _ (directed_mem (adj_symm iv)) _ (directed_mem vj) ne2)
    intro u
    by_cases hi : i ∈ u <;> by_cases hj : j ∈ u <;> by_cases hv : v ∈ u <;>
      simp [asWord,directed,apart,hi,hj,hv]

def coeff (i j : Fin n) : ℤ := if j = i then 1 else 0

def value (b : Bool) : ℤ := if b then 1 else 0

def oddPart (f : F n) (x : W n) : ℤ := value (asWord f x) - value (asWord f xᶜ)

def affine (f : F n) := ∃ b : ℤ, ∃ a : Fin n → ℤ, ∀ x : W n, oddPart f x = b + x.sum a

lemma coord (i : Fin n) (x : W n) : x.sum (coeff i) = if i ∈ x then 1 else 0 := by
  classical
  change (∑ j ∈ x, if j = i then (1 : ℤ) else 0) = _
  exact Finset.sum_ite_eq' x i (fun _ => (1 : ℤ))

lemma generators (E : Finset (Edge n)) (f : F n) (hf : f ∈ target E ∪ raw E) : affine f := by
  classical
  simp only [Finset.mem_union, target, raw, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_insert,Finset.mem_singleton] at hf
  rcases hf with (((⟨i,rfl⟩|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩) |
    ((((rfl|rfl)|⟨i,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩)
  · refine ⟨1,fun t => -(coeff i t + coeff i t),?_⟩
    intro x; by_cases h : i ∈ x <;> simp [oddPart,asWord,neg,value,Finset.sum_add_distrib,coord,h]
  · refine ⟨1,fun t => -(coeff i t + coeff j t),?_⟩
    intro x; by_cases h : i ∈ x <;> by_cases h' : j ∈ x <;>
      simp [oddPart,asWord,zz,value,Finset.sum_add_distrib,coord,h,h']
  · refine ⟨0,fun t => coeff i t - coeff j t,?_⟩
    intro x; by_cases h : i ∈ x <;> by_cases h' : j ∈ x <;>
      simp [oddPart,asWord,oz,value,Finset.sum_sub_distrib,coord,h,h']
  · refine ⟨0,fun t => coeff j t - coeff i t,?_⟩
    intro x; by_cases h : i ∈ x <;> by_cases h' : j ∈ x <;>
      simp [oddPart,asWord,zo,value,Finset.sum_sub_distrib,coord,h,h']
  · exact ⟨0,fun _ => 0,by simp [oddPart,asWord]⟩
  · exact ⟨0,fun _ => 0,by simp [oddPart,asWord]⟩
  · refine ⟨-1,fun t => coeff i t + coeff i t,?_⟩
    intro x; by_cases h : i ∈ x <;> simp [oddPart,asWord,pos,value,Finset.sum_add_distrib,coord,h]
  · refine ⟨0,fun _ => 0,?_⟩
    intro x; by_cases h : i ∈ x <;> by_cases h' : j ∈ x <;> simp [oddPart,asWord,eqBit,h,h']
  · refine ⟨0,fun _ => 0,?_⟩
    intro x; by_cases h : i ∈ x <;> by_cases h' : j ∈ x <;> simp [oddPart,asWord,xorBit,h,h']

lemma targetSign (E : Finset (Edge n)) (f : F n) (hf : f ∈ target E) (x : W n) :
    asWord f x = true ↔ 0 < oddPart f x := by
  classical
  simp only [target, Finset.mem_union, Finset.mem_image, Finset.mem_univ,true_and] at hf
  rcases hf with ((⟨i,rfl⟩|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩
  · by_cases h : i ∈ x <;> simp [asWord,neg,oddPart,value,h]
  all_goals by_cases h : i ∈ x <;> by_cases hh : j ∈ x <;>
    simp [asWord,zz,oz,zo,oddPart,value,h,hh]

lemma targetLive (E : Finset (Edge n)) (sorted : ∀ e ∈ E, e.1 < e.2)
    (f : F n) (hf : f ∈ target E) : (∃ x, asWord f x = true) ∧ asWord f Finset.univ = false := by
  classical
  simp only [target, Finset.mem_union, Finset.mem_image, Finset.mem_univ,true_and] at hf
  rcases hf with ((⟨i,rfl⟩|⟨⟨i,j⟩,he,rfl⟩)|⟨⟨i,j⟩,he,rfl⟩)|⟨⟨i,j⟩,he,rfl⟩
  · exact ⟨⟨∅,by simp [asWord,neg]⟩,by simp [asWord,neg]⟩
  · exact ⟨⟨∅,by simp [asWord,zz]⟩,by simp [asWord,zz]⟩
  · have h : i < j := sorted _ he
    exact ⟨⟨{i},by simp [asWord,oz,h.ne']⟩,by simp [asWord,oz]⟩
  · have h : i < j := sorted _ he
    exact ⟨⟨{j},by simp [asWord,zo,h.ne]⟩,by simp [asWord,zo]⟩

lemma oddTargetNe (E : Finset (Edge n)) (f g : F n) (hf : f ∈ target E)
    (hg : g ∈ target E) (hne : f ≠ g) : ∃ x, oddPart f x ≠ oddPart g x := by
  classical
  by_contra! same
  apply hne
  funext b
  let x := Finset.univ.filter (fun i => b i = true)
  have hx : (fun i => decide (i ∈ x)) = b := by funext i; simp [x]
  change f b = g b
  rw [←hx]
  exact Bool.eq_iff_iff.mpr ((targetSign E f hf x).trans ((same x) ▸ (targetSign E g hg x).symm))

lemma oddRawNe (E : Finset (Edge n)) (sorted : ∀ e ∈ E, e.1 < e.2)
    (f g : F n) (hf : f ∈ target E) (hg : g ∈ raw E)
    (hu : asWord f Finset.univ = asWord g Finset.univ) : ∃ x, oddPart f x ≠ oddPart g x := by
  classical
  obtain ⟨⟨x,hx⟩,h1⟩ := targetLive E sorted f hf
  have hp := (targetSign E f hf x).mp hx
  refine ⟨x,?_⟩
  suffices zero : oddPart g x = 0 by omega
  simp only [raw, Finset.mem_union, Finset.mem_image, Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton] at hg
  rcases hg with (((rfl|rfl)|⟨i,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩)|⟨⟨i,j⟩,_,rfl⟩
  · simp [asWord,oddPart]
  · simp [asWord,oddPart]
  · rw [h1] at hu
    simp [asWord,pos] at hu
  all_goals by_cases h : i ∈ x <;> by_cases hh : j ∈ x <;> simp [oddPart,asWord,eqBit,xorBit,h,hh]

def flip (i j : Fin n) := (Equiv.swap i j).finsetCongr

def invert (n : Nat) : W n ≃ W n := ⟨(·ᶜ),(·ᶜ),compl_compl,compl_compl⟩

lemma flipSum (a : Fin n → ℤ) (i j : Fin n) (ne : i ≠ j) (x : W n) :
    (flip i j x).sum a = x.sum a + (if i ∈ x then a j - a i else 0) +
      (if j ∈ x then a i - a j else 0) := by
  classical
  have eq (t : Fin n) : a (Equiv.swap i j t) = a t +
      (if i = t then a j-a i else 0) + (if j = t then a i-a j else 0) := by
    by_cases hi : t = i
    · subst t; simp [ne.symm]
    by_cases hj : t = j
    · subst t; simp [ne]
    simp [Equiv.swap_apply_of_ne_of_ne hi hj,Ne.symm hi,Ne.symm hj]
  simp [flip,Equiv.finsetCongr_apply,Finset.sum_map,eq,Finset.sum_add_distrib]

noncomputable def err (f g : F n) (x : W n) : Nat := if asWord f x = asWord g x then 0 else 1

lemma affineDistance (f g : F n) (hf : affine f) (hg : affine g)
    (same0 : asWord f ∅ = asWord g ∅) (same1 : asWord f Finset.univ = asWord g Finset.univ)
    (diff : ∃ x, oddPart f x ≠ oddPart g x) :
    ∃ i j : Fin n, i ≠ j ∧ ∀ x : W n, (if apart i j x then 2 else 0) ≤
      err f g x + err f g xᶜ + err f g (flip i j x) + err f g (flip i j x)ᶜ := by
  classical
  obtain ⟨b,c,hc⟩ := hf
  obtain ⟨d,e,he⟩ := hg
  let a (t : Fin n) := c t - e t
  have bd : b=d := by
    have s := hc ∅; have t := he ∅
    simp only [oddPart,Finset.compl_empty,Finset.sum_empty,add_zero,same0,same1] at s t
    omega
  have lin (x : W n) : oddPart f x - oddPart g x = x.sum a := by
    rw [hc,he,bd,Finset.sum_sub_distrib]; abel
  have total : ∑ t, a t = 0 := by
    rw [←lin]; simp [oddPart,same0,same1]
  have nz : ∃ t ∈ Finset.univ, a t ≠ 0 := by
    by_contra! h
    obtain ⟨x,hx⟩ := diff
    have eq := lin x
    have zero : x.sum a = 0 := by
      apply Finset.sum_eq_zero; intro t _; apply h <;> simp
    exact hx (sub_eq_zero.mp (eq.trans zero))
  obtain ⟨i,_,hi⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero a total nz
  have minus : ∑ t, -a t = 0 := by simp [total]
  obtain ⟨j,_,hj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero (fun t => -a t) minus
    (by simpa using nz)
  have ne : i ≠ j := by rintro rfl; omega
  refine ⟨i,j,ne,fun x => ?_⟩
  have swapEq := flipSum a i j ne x
  rw [←lin,←lin] at swapEq
  have bound (u : W n) : -(err f g u : ℤ) ≤ value (asWord f u)-value (asWord g u) ∧
      value (asWord f u)-value (asWord g u) ≤ (err f g u : ℤ) := by
    unfold err; cases asWord f u <;> cases asWord g u <;> decide
  have h₁ := bound x; have h₂ := bound xᶜ
  have h₃ := bound (flip i j x); have h₄ := bound (flip i j x)ᶜ
  unfold oddPart at swapEq
  by_cases mem : i ∈ x <;> by_cases mem' : j ∈ x <;> simp [apart,mem,mem'] at swapEq ⊢ <;> omega

lemma weightedPerm (p : W n ≃ W n) (w h : W n → Nat) (inv : ∀ x, w (p x) = w x) :
    (∑ x, w x * h (p x)) = ∑ x, w x * h x := by
  calc
    _ = ∑ x, w (p x) * h (p x) := by simp_rw [inv]
    _ = _ := p.sum_comp (fun x => w x * h x)

lemma marginBound (w : W n → Nat) (f g : F n) (i j : Fin n)
    (co : ∀ x : W n, w xᶜ = w x) (sw : ∀ x, w (flip i j x) = w x)
    (bound : ∀ x : W n, (if apart i j x then 2 else 0) ≤
      err f g x + err f g xᶜ + err f g (flip i j x) + err f g (flip i j x)ᶜ) :
    distance w i j ≤ 2 * margin Finset.univ w f g := by
  classical
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => Nat.mul_le_mul_left (w x) (bound x))
  have lhs : (∑ x, w x * (if apart i j x then 2 else 0)) = distance w i j * 2 := by
    simp [distance,Finset.sum_filter,Finset.sum_mul,mul_ite,ite_mul]
  have rhs : (∑ x, w x * err f g x) = margin Finset.univ w f g := by
    simp [margin,Finset.sum_filter,err,mul_ite,ite_not]
  have cmp := weightedPerm (invert n) w (err f g) co
  change (∑ x, w x * err f g xᶜ) = _ at cmp
  have flip1 := weightedPerm (flip i j) w (err f g) sw
  have flip2 := weightedPerm (flip i j) w (fun x => err f g xᶜ) sw
  simp only [Nat.mul_add,Finset.sum_add_distrib,lhs,flip1,flip2,cmp,rhs] at sum
  omega

def layer (k : Nat) (x : W n) : Nat := if x.card = k then 1 else 0

def uniform (x : W n) := x = ∅ ∨ x = Finset.univ

noncomputable def sample (D scale : Nat) (x : W n) :=
  (if uniform x then D else 0) + scale * (layer (n/2) x + layer (n/2) xᶜ)

lemma layerCount (hn : 2 ≤ n) (i j : Fin n) (ne : i ≠ j) :
    (∑ x : W n, if i ∈ x ∧ j ∉ x then layer (n/2) x else 0) =
      Nat.choose (n-2) (n/2-1) := by
  classical
  let t := (Finset.univ : W n).erase j
  have sub : ({i} : W n) ⊆ t := by simp [t,ne]
  have enough : ({i} : W n).card ≤ n/2 := by simp; omega
  have count := Finset.card_filter_powersetCard_subset {i} t (n/2) sub enough
  have eq : ∀ x : W n, (if i ∈ x ∧ j ∉ x then layer (n/2) x else 0) =
      if x ∈ (t.powersetCard (n/2)).filter ({i} ⊆ ·) then 1 else 0 := by
    intro x
    have inside : x ⊆ t ↔ j ∉ x := by simp [t,Finset.subset_iff]
    by_cases a : i ∈ x <;> by_cases b : j ∈ x <;> by_cases c : x.card=n/2 <;>
      simp [Finset.mem_powersetCard,inside,layer,a,b,c]
  simp_rw [eq]
  rw [Finset.sum_boole,Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]
  simpa [t,Finset.card_erase_of_mem,Nat.sub_sub] using count

lemma sampleCo (D scale : Nat) (x : W n) : sample D scale xᶜ = sample D scale x := by
  have eq : uniform xᶜ ↔ uniform x := by simp [uniform,or_comm]
  simp only [sample,eq,compl_compl]; rw [Nat.add_comm (layer _ xᶜ)]

lemma sampleSw (D scale : Nat) (i j : Fin n) (x : W n) :
    sample D scale (flip i j x) = sample D scale x := by
  classical
  have all (z : W n) : z = Finset.univ ↔ z.card = n := by
    simpa using (Finset.card_eq_iff_eq_univ (s := z)).symm
  simp [sample,layer,uniform,all,←Finset.card_eq_zero,flip,Equiv.finsetCongr_apply,Finset.card_compl]

lemma sampleAnchor (hn : 2 ≤ n) (D scale : Nat) :
    sample D scale (∅ : W n) = D ∧ sample D scale (Finset.univ : W n) = D := by
  have h : n ≠ n/2 := by omega
  have h' : 0 ≠ n/2 := by omega
  simp [sample,layer,uniform,h,h']

lemma sampleDistance (hn : 2 ≤ n) (D scale : Nat) (i j : Fin n) (ne : i ≠ j) :
    distance (sample D scale) i j = 2 * (2 * Nat.choose (n-2) (n/2-1)) * scale := by
  classical
  let v (x : W n) := if apart i j x then layer (n/2) x else 0
  have count : (∑ x, v x) = 2 * Nat.choose (n-2) (n/2-1) := by
    have eq (x : W n) : v x = (if i ∈ x ∧ j ∉ x then layer (n/2) x else 0) +
        (if j ∈ x ∧ i ∉ x then layer (n/2) x else 0) := by
      by_cases a : i ∈ x <;> by_cases b : j ∈ x <;> simp [v,apart,a,b]
    simp_rw [eq,Finset.sum_add_distrib,layerCount hn i j ne,layerCount hn j i ne.symm]
    omega
  have eq (x : W n) : (if apart i j x then sample D scale x else 0) = scale * (v x + v xᶜ) := by
    by_cases h : apart i j x
    · have nu : ¬ uniform x := by rintro (rfl|rfl) <;> simp [apart] at h
      have hc : apart i j xᶜ := by simpa [apart,not_iff_not] using h
      simp [sample,v,h,hc,nu]
    · have hc : ¬ apart i j xᶜ := by simpa [apart,not_iff_not] using h
      simp [v,h,hc]
  have co : (∑ x : W n, v xᶜ) = ∑ x, v x := (invert n).sum_comp v
  simp only [distance,Finset.sum_filter,eq,←Finset.mul_sum,Finset.sum_add_distrib,co,count]
  ring

lemma sampleGood (hn : 2 ≤ n) (E : Finset (Edge n)) (sorted : ∀ e ∈ E, e.1 < e.2)
    (conn : connected E) (D scale : Nat) (hd : D ≤ (2*Nat.choose (n-2) (n/2-1))*scale) :
    validBank E D (sample D scale) := by
  classical
  let w : W n → Nat := sample D scale
  have anc := sampleAnchor hn D scale
  apply (bankIff n hn E sorted conn D w).mpr
  refine ⟨⟨anc.1.ge,anc.2.ge⟩,?_⟩
  have go (f g : F n) (hf : f ∈ target E) (hg : g ∈ target E ∪ raw E)
      (hdiff : asWord f Finset.univ = asWord g Finset.univ → ∃ x, oddPart f x ≠ oddPart g x) :
      D ≤ margin Finset.univ w f g := by
    have anchor (z : W n) (hz : w z = D) (ne : asWord f z ≠ asWord g z) :
        D ≤ margin Finset.univ w f g := by
      rw [←hz]
      apply Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
      simp [ne]
    by_cases h0 : asWord f ∅ = asWord g ∅
    · by_cases h1 : asWord f Finset.univ = asWord g Finset.univ
      · obtain ⟨i,j,ne,bound⟩ := affineDistance f g (generators E f (Finset.mem_union_left _ hf))
          (generators E g hg) h0 h1 (hdiff h1)
        have le := marginBound w f g i j (sampleCo D scale) (sampleSw D scale i j) bound
        rw [show distance w i j = _ from sampleDistance hn D scale i j ne] at le
        rw [Nat.mul_assoc] at le
        exact hd.trans (by omega)
      · exact anchor _ anc.2 h1
    · exact anchor _ anc.1 h0
  exact ⟨fun f hf g hg ne => go f g hf (Finset.mem_union_left _ hg) (fun _ => oddTargetNe E f g hf hg ne),
    fun f hf g hg => go f g hf (Finset.mem_union_right _ hg) (oddRawNe E sorted f g hf hg)⟩

def pairs (n : Nat) := (Finset.univ : Finset (Edge n)).filter (fun e => e.1 < e.2)

def mixed (n : Nat) := (Finset.univ : Finset (W n)).filter (fun x => x ≠ ∅ ∧ x ≠ Finset.univ)

def maxCut (n : Nat) := (n/2)*(n-n/2)

def cut (x : W n) := x.card*(n-x.card)

lemma cutBound (x : W n) : cut x ≤ maxCut n := by
  have le : x.card ≤ n := by simpa using Finset.card_le_univ x
  unfold cut maxCut
  by_cases h : x.card ≤ n/2
  · have : n/2 ≤ n-x.card := by omega
    have eq : n/2*(n-n/2) = x.card*(n-x.card) + (n/2-x.card)*(n-n/2-x.card) := by
      zify [le,h,show n/2 ≤ n by omega,show x.card ≤ n-n/2 by omega]; ring
    omega
  · have eq : n/2*(n-n/2) = x.card*(n-x.card) + (x.card-n/2)*(x.card-(n-n/2)) := by
      zify [le,show n/2 ≤ x.card by omega,show n-n/2 ≤ x.card by omega,show n/2 ≤ n by omega]; ring
    omega

lemma cutCard (x : W n) : ((pairs n).filter (fun e => apart e.1 e.2 x)).card = cut x := by
  classical
  suffices eq : ((pairs n).filter (fun e => apart e.1 e.2 x)).card = (x ×ˢ xᶜ).card by
    simpa [cut,Finset.card_compl] using eq
  apply Finset.card_nbij' (fun e => if e.1 ∈ x then e else e.swap)
    (fun e => if e.1 < e.2 then e else e.swap)
  all_goals
    rintro ⟨i,j⟩ h
    simp [pairs,apart] at h
    simp [pairs,apart] <;> split_ifs <;> (try simp_all) <;> grind [pairs,apart]

lemma charge (w : W n → Nat) :
    (∑ e ∈ pairs n, distance w e.1 e.2) = ∑ x ∈ mixed n, w x * cut x := by
  classical
  unfold distance mixed
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have count : (∑ e ∈ pairs n, if apart e.1 e.2 x then w x else 0) = w x * cut x := by
    rw [←Finset.sum_filter,Finset.sum_const,cutCard,smul_eq_mul,Nat.mul_comm]
  rw [count]
  by_cases he : x = ∅ <;> by_cases hu : x = Finset.univ <;> simp_all [cut]

lemma mass (hn : 2 ≤ n) (w : W n → Nat) :
    (∑ x, w x) = w ∅ + w Finset.univ + (mixed n).sum w := by
  classical
  have ne : (∅ : W n) ≠ Finset.univ := by
    intro eq
    have h := congrArg Finset.card eq
    simp at h; omega
  have split (x : W n) : w x = (if x = ∅ then w ∅ else 0) +
      (if x = Finset.univ then w Finset.univ else 0) +
        (if x ≠ ∅ ∧ x ≠ Finset.univ then w x else 0) := by
    by_cases he : x = ∅ <;> by_cases hu : x = Finset.univ <;> simp_all
  calc
    _ = ∑ x : W n, ((if x = ∅ then w ∅ else 0) +
          (if x = Finset.univ then w Finset.univ else 0) +
          (if x ≠ ∅ ∧ x ≠ Finset.univ then w x else 0)) := Finset.sum_congr rfl (fun x _ => split x)
    _ = _ := by simp [mixed,Finset.sum_filter,Finset.sum_add_distrib]

lemma samplePrice (hn : 2 ≤ n) (D scale : Nat) :
    (mixed n).sum (sample D scale) * maxCut n =
      (pairs n).card * (2 * (2*Nat.choose (n-2) (n/2-1)) * scale) := by
  classical
  have sc (x : W n) (hx : x ∈ mixed n) : sample D scale x * maxCut n = sample D scale x * cut x := by
    have nu : ¬ uniform x := by simpa [mixed,uniform,not_or] using hx
    by_cases hk : x.card = n/2
    · simp [cut,maxCut,hk]
    by_cases hc : xᶜ.card = n/2
    · have le : x.card ≤ n := by simpa using Finset.card_le_univ x
      have hv : n-x.card = n/2 := by simpa [Finset.card_compl] using hc
      have hv' : x.card = n-n/2 := by omega
      unfold cut maxCut; rw [hv,hv']; ring
    simp [sample,nu,layer,hk,hc]
  rw [Finset.sum_mul,Finset.sum_congr rfl sc,←charge]
  have h (e : Edge n) (he : e ∈ pairs n) := sampleDistance hn D scale e.1 e.2
    (show e.1 ≠ e.2 from ((Finset.mem_filter.mp he).2 : e.1 < e.2).ne)
  rw [Finset.sum_congr rfl h,Finset.sum_const,smul_eq_mul]

lemma rounded (D Q : Nat) (posQ : 0 < Q) : ∃ scale, Q*scale = D + ((Q-D%Q)%Q) := by
  have base := Nat.mod_add_div D Q
  have lt := Nat.mod_lt D posQ
  by_cases hz : D%Q=0
  · refine ⟨D/Q,?_⟩; simpa [hz] using base
  · refine ⟨D/Q+1,?_⟩
    rw [Nat.mul_add,Nat.mul_one,Nat.mod_eq_of_lt (show Q-D%Q < Q by omega)]
    omega

lemma deficit (hn : 2 ≤ n) (E : Finset (Edge n)) (sorted : ∀ e ∈ E, e.1 < e.2)
    (conn : connected E) (diam : ∀ i j, i ≠ j → adj E i j ∨ ∃ v, adj E i v ∧ adj E v j)
    (D : Nat) (w : W n → Nat) (good : validBank E D w)
    (opt : ∀ u, validBank E D u → (∑ x, w x) ≤ ∑ x, u x) :
    w ∅ = D ∧ w Finset.univ = D ∧ (∀ e ∈ pairs n, 2*D ≤ distance w e.1 e.2) ∧
    (∑ x ∈ mixed n, w x * (maxCut n - cut x)) +
    (∑ e ∈ pairs n, (distance w e.1 e.2 - 2*D)) ≤
      2*(pairs n).card*(((2*Nat.choose (n-2) (n/2-1))-D%(2*Nat.choose (n-2) (n/2-1)))%
        (2*Nat.choose (n-2) (n/2-1))) := by
  classical
  obtain ⟨⟨he,hu⟩,hm⟩ := (bankIff n hn E sorted conn D w).mp good
  have empty := Nat.le_antisymm (clipped E D w good opt ∅) he
  have full := Nat.le_antisymm (clipped E D w good opt Finset.univ) hu
  have lb (e : Edge n) (he : e ∈ pairs n) : 2*D ≤ distance w e.1 e.2 := by
    have ne := ((Finset.mem_filter.mp he).2 : e.1 < e.2).ne
    exact targetDistance E sorted D w hm _ _ ne (diam _ _ ne)
  refine ⟨empty,full,lb,?_⟩
  let Q := 2*Nat.choose (n-2) (n/2-1)
  have pq : 0 < Q := Nat.mul_pos (by decide) (Nat.choose_pos (by omega))
  obtain ⟨t,ht⟩ := rounded D Q pq
  have feasible := sampleGood hn E sorted conn D t (show D ≤ Q*t by omega)
  have mon := opt _ feasible
  rw [mass hn w,mass hn (sample D t),empty,full,(sampleAnchor hn D t).1,(sampleAnchor hn D t).2] at mon
  have upper := Nat.mul_le_mul_right (maxCut n) (show (mixed n).sum w ≤ (mixed n).sum (sample D t) by omega)
  rw [samplePrice hn D t] at upper
  have eq1 : (∑ x ∈ mixed n, w x * (maxCut n-cut x)) + (∑ x ∈ mixed n, w x * cut x) =
      (mixed n).sum w * maxCut n := by
    rw [←Finset.sum_add_distrib,Finset.sum_mul]; apply Finset.sum_congr rfl
    intro x _; rw [←Nat.mul_add,Nat.sub_add_cancel (cutBound x)]
  have eq2 : (∑ e ∈ pairs n, (distance w e.1 e.2-2*D)) + (pairs n).card*(2*D) =
      ∑ e ∈ pairs n, distance w e.1 e.2 := by
    have const : (pairs n).card*(2*D) = ∑ _ ∈ pairs n, 2*D := by simp
    rw [const,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro e he; exact Nat.sub_add_cancel (lb e he)
  rw [charge] at eq2
  have up : (pairs n).card * (2 * Q * t) = (pairs n).card * (2*D) + 2*(pairs n).card*((Q-D%Q)%Q) := by
    rw [Nat.mul_assoc,ht]; ring
  change _ ≤ (pairs n).card * (2 * Q * t) at upper
  rw [up] at upper
  change _ ≤ 2*(pairs n).card*((Q-D%Q)%Q)
  omega

end PEqualNP.Outside.L_meta_53208

open PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_53208 : (∀ (n : Nat) (E : Finset (Fin n × Fin n)), 2 ≤ n →
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
  let adj := fun i j : Fin n => (i,j) ∈ E ∨ (j,i) ∈ E
  (∀ i j : Fin n, i ≠ j → adj i j ∨ ∃ v, adj i v ∧ adj v j) →
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)
  let mixed := (Finset.univ : Finset W).filter (fun x => x ≠ ∅ ∧ x ≠ Finset.univ)
  let K := (n/2)*(n-n/2)
  let Q := 2 * Nat.choose (n-2) (n/2-1)
  ∀ (D : Nat) (w : W → Nat), 0 < D → valid D w →
    (∀ u : W → Nat, valid D u → (∑ x, w x) ≤ ∑ x, u x) →
    let dist := fun e : Fin n × Fin n =>
      ((Finset.univ : Finset W).filter (fun x => ¬ (e.1 ∈ x ↔ e.2 ∈ x))).sum w
    w ∅ = D ∧ w Finset.univ = D ∧ (∀ e ∈ pairs, 2*D ≤ dist e) ∧
      (∑ x ∈ mixed, w x * (K - x.card*(n-x.card))) +
        (∑ e ∈ pairs, (dist e - 2*D)) ≤ 2*pairs.card*((Q - D % Q) % Q)) := by
  classical
  intro n E hn sorted conn
  dsimp only
  intro diam D w _ good opt
  have invEq : PEqualNP.GraphSeedSamples.inv (n := n) =
      fun (i : Fin n) (x : Finset (Fin n)) => !(decide (i ∈ x)) := by
    funext i x; by_cases h : i ∈ x <;> simp [PEqualNP.GraphSeedSamples.inv,h]
  have sameEq : PEqualNP.GraphSeedSamples.same (n := n) = fun e x =>
      decide (e.1 ∈ x) == decide (e.2 ∈ x) := by
    funext e x; by_cases h : e.1 ∈ x <;> by_cases h' : e.2 ∈ x <;> simp [PEqualNP.GraphSeedSamples.same,h,h']
  have cover (S : Finset (Fin n)) : PEqualNP.GraphSeedSamples.cover L_meta_53208.oneColor S ↔ S.Nonempty := by
    constructor
    · intro h; obtain ⟨i,hi,_⟩ := h 0; exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩ j; exact ⟨i,hi,Subsingleton.elim ..⟩
  have bitOk (i : Fin n) (x : Finset (Fin n)) {d : Decidable (i ∈ x)} :
      PEqualNP.GraphSeedSamples.bit i x = @decide (i ∈ x) d := by
    by_cases h : i ∈ x <;> simp [PEqualNP.GraphSeedSamples.bit,h]
  have crossOk (e : Fin n × Fin n) (x : Finset (Fin n)) {d : Decidable (e.1 ∈ x)}
      {d' : Decidable (e.2 ∈ x)} {deq : DecidableEq Bool} : PEqualNP.GraphSeedSamples.cross e x =
      !(@BEq.beq Bool (@instBEqOfDecidableEq Bool deq) (@decide (e.1 ∈ x) d) (@decide (e.2 ∈ x) d')) := by
    by_cases h : e.1 ∈ x <;> by_cases h' : e.2 ∈ x <;>
      simp [PEqualNP.GraphSeedSamples.cross,PEqualNP.GraphSeedSamples.same,instBEqOfDecidableEq,h,h']
  have good' : L_meta_53208.validBank E D w := by
    unfold L_meta_53208.validBank PEqualNP.GraphSampleDistance.keeps
    simp only [PEqualNP.GraphSampleDistance.fitsAt,PEqualNP.GraphSampleDistance.wire,
      PEqualNP.GraphSeedSamples.bank,PEqualNP.GraphSeedSamples.bit,PEqualNP.GraphSeedSamples.cross,
      invEq,sameEq,cover,PEqualNP.GraphSampleDistance.req,PEqualNP.GraphInversionSeeds.target,
      Finset.image_union,Finset.image_image,Function.comp_def,PEqualNP.GraphSampleDistance.asWord,
      PEqualNP.GraphInversionSeeds.neg,PEqualNP.GraphInversionSeeds.zz,
      PEqualNP.GraphInversionSeeds.oz,PEqualNP.GraphInversionSeeds.zo]
    convert! good using 0 <;> congr! 80 <;> first | apply bitOk | apply crossOk
  have opt' : ∀ u, L_meta_53208.validBank E D u → (∑ x, w x) ≤ ∑ x, u x := by
    intro u hu
    apply opt u
    simp only [L_meta_53208.validBank,PEqualNP.GraphSampleDistance.keeps,
      PEqualNP.GraphSampleDistance.fitsAt,PEqualNP.GraphSampleDistance.wire,
      PEqualNP.GraphSeedSamples.bank,PEqualNP.GraphSeedSamples.bit,PEqualNP.GraphSeedSamples.cross,
      invEq,sameEq,cover,PEqualNP.GraphSampleDistance.req,PEqualNP.GraphInversionSeeds.target,
      Finset.image_union,Finset.image_image,Function.comp_def,PEqualNP.GraphSampleDistance.asWord,
      PEqualNP.GraphInversionSeeds.neg,PEqualNP.GraphInversionSeeds.zz,
      PEqualNP.GraphInversionSeeds.oz,PEqualNP.GraphInversionSeeds.zo] at hu
    convert! hu using 0 <;> congr! 80 <;> symm <;> first | apply bitOk | apply crossOk
  have out := L_meta_53208.deficit hn E sorted conn diam D w good' opt'
  unfold L_meta_53208.distance L_meta_53208.apart L_meta_53208.maxCut L_meta_53208.pairs
    L_meta_53208.mixed L_meta_53208.cut at out
  first | exact out | convert! out using 0 <;> congr! 80
