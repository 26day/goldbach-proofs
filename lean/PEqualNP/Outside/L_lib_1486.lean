import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1486_aux

def fam (k : ℕ) (x : Fin (2*k)) : Finset (Finset (Fin (2*k))) :=
  insert {x} ((Finset.Ico 2 k).biUnion (fun j => Finset.powersetCard j Finset.univ))

theorem fam_card (k : ℕ) (x : Fin (2*k)) :
    (fam k x).card = (∑ j ∈ Finset.Ico 2 k, Nat.choose (2*k) j) + 1 := by
  unfold fam
  rw [Finset.card_insert_of_notMem, Finset.card_biUnion]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    exact Finset.disjoint_left.2 (fun S h1 h2 =>
      hij ((Finset.mem_powersetCard.1 h1).2.symm.trans (Finset.mem_powersetCard.1 h2).2))
  · intro h
    rw [Finset.mem_biUnion] at h
    obtain ⟨j, hj, hS⟩ := h
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_Ico] at hj
    have := hS.2
    rw [Finset.card_singleton] at this
    omega

theorem mem_fam {k : ℕ} {x : Fin (2*k)} {S : Finset (Fin (2*k))} (h : S ∈ fam k x) :
    S = {x} ∨ (2 ≤ S.card ∧ S.card < k) := by
  unfold fam at h
  rw [Finset.mem_insert, Finset.mem_biUnion] at h
  rcases h with h | ⟨j, hj, hS⟩
  · exact Or.inl h
  · rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_Ico] at hj
    obtain ⟨_, hc⟩ := hS
    exact Or.inr ⟨by omega, by omega⟩

theorem fam_size {k : ℕ} (hk : 4 ≤ k) {x : Fin (2*k)} {S : Finset (Fin (2*k))} (h : S ∈ fam k x) :
    1 ≤ S.card ∧ S.card + 1 ≤ k ∧ (S.card = 1 → S = {x}) := by
  rcases mem_fam h with rfl | ⟨h1, h2⟩
  · rw [Finset.card_singleton]
    exact ⟨le_refl _, by omega, fun _ => rfl⟩
  · exact ⟨by omega, by omega, fun h3 => by omega⟩

def up {k : ℕ} (x : Fin (2*k)) (S : Finset (Fin (2*k))) : Finset (Finset (Fin (2*k))) :=
  (Finset.univ.filter (fun y => y ∉ S ∧ y ≠ x)).image (fun y => insert y S)

theorem mem_up {k : ℕ} {x : Fin (2*k)} {S T : Finset (Fin (2*k))} :
    T ∈ up x S ↔ ∃ y, (y ∉ S ∧ y ≠ x) ∧ insert y S = T := by
  unfold up
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_up {k : ℕ} (x : Fin (2*k)) (S : Finset (Fin (2*k))) (hS : S.card + 1 ≤ k) :
    k ≤ (up x S).card := by
  unfold up
  rw [Finset.card_image_of_injOn]
  · have he : (Finset.univ.filter (fun y => y ∉ S ∧ y ≠ x)) = Finset.univ \ insert x S := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_insert, not_or]
      tauto
    rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have := Finset.card_insert_le x S
    omega
  · intro y1 hy1 y2 hy2 he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy1 hy2
    have : y1 ∈ insert y2 S := by
      have h' : y1 ∈ insert y1 S := Finset.mem_insert_self y1 S
      simp only at he
      rw [he] at h'
      exact h'
    rcases Finset.mem_insert.1 this with h | h
    · exact h
    · exact absurd h hy1.1

theorem hall_fam (k : ℕ) (hk : 4 ≤ k) (x : Fin (2*k)) :
    ∃ φ : (fam k x) → Finset (Fin (2*k)), Function.Injective φ ∧
      ∀ S, ∃ y, y ∉ S.1 ∧ y ≠ x ∧ φ S = insert y S.1 := by
  have hall : ∀ s : Finset (fam k x), s.card ≤ (s.biUnion (fun S => up x S.1)).card := by
    intro s
    have key := Finset.card_mul_le_card_mul (fun (S : fam k x) (T : Finset (Fin (2*k))) => T ∈ up x S.1)
      (s := s) (t := s.biUnion (fun S => up x S.1)) (m := k) (n := k) ?_ ?_
    · exact Nat.le_of_mul_le_mul_right key (by omega)
    · intro S hS
      have hsub : up x S.1 ⊆ (s.biUnion (fun S => up x S.1)).bipartiteAbove (fun S T => T ∈ up x S.1) S := by
        intro T hT
        rw [Finset.mem_bipartiteAbove]
        exact ⟨Finset.mem_biUnion.2 ⟨S, hS, hT⟩, hT⟩
      exact le_trans (card_up x S.1 (fam_size hk S.2).2.1) (Finset.card_le_card hsub)
    · intro T hT
      obtain ⟨S0, _, hT0⟩ := Finset.mem_biUnion.1 hT
      obtain ⟨y0, ⟨hy0, _⟩, hT0'⟩ := mem_up.1 hT0
      have hTc : T.card ≤ k := by
        rw [← hT0', Finset.card_insert_of_notMem hy0]
        exact (fam_size hk S0.2).2.1
      have := Finset.card_le_card_of_injOn (fun S : fam k x => S.1)
        (s := s.bipartiteBelow (fun S T => T ∈ up x S.1) T) (t := (T.erase x).image (fun y => T.erase y))
        (by
          intro S hS
          rw [Finset.coe_bipartiteBelow] at hS
          obtain ⟨_, hS2⟩ := hS
          obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := mem_up.1 hS2
          rw [Finset.coe_image]
          refine ⟨y, Finset.mem_erase.2 ⟨hy2, by rw [← hy3]; exact Finset.mem_insert_self y S.1⟩, ?_⟩
          show T.erase y = S.1
          rw [← hy3, Finset.erase_insert hy1])
        (by
          intro a _ b _ hab
          exact Subtype.ext hab)
      exact le_trans this (le_trans Finset.card_image_le (le_trans (Finset.card_erase_le) hTc))
  obtain ⟨φ, hφ, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective (fun S : fam k x => up x S.1)).1 hall
  refine ⟨φ, hφ, fun S => ?_⟩
  obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := mem_up.1 (hmem S)
  exact ⟨y, hy1, hy2, hy3.symm⟩


theorem main_aux (k m : ℕ) (hk : 4 ≤ k) (hm : m ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose (2*k) j) + 1) :
    ∃ f : Fin m × Bool → Finset (Fin (2*k)),
      Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
      (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧ f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
      ∀ a i, f a ≠ f (i,false) ∪ f (i,true) ∧ f a ≠ Finset.univ \ (f (i,false) ∪ f (i,true)) := by
  let x : Fin (2*k) := ⟨0, by omega⟩
  obtain ⟨φ, hφ, hφy⟩ := hall_fam k hk x
  have hcard : m ≤ (fam k x).card := by rw [fam_card k x]; exact hm
  let e : Fin m → fam k x := fun i => (fam k x).equivFin.symm (Fin.castLE hcard i)
  have he : Function.Injective e := (fam k x).equivFin.symm.injective.comp (Fin.castLE_injective hcard)
  choose y hy1 hy2 hy3 using hφy
  let f : Fin m × Bool → Finset (Fin (2*k)) := fun a =>
    if a.2 then Finset.univ \ insert (y (e a.1)) (e a.1).1 else (e a.1).1
  have hf0 : ∀ i, f (i, false) = (e i).1 := fun i => rfl
  have hf1 : ∀ i, f (i, true) = Finset.univ \ insert (y (e i)) (e i).1 := fun i => rfl
  have hsz : ∀ i, 1 ≤ (e i).1.card ∧ (e i).1.card + 1 ≤ k ∧ ((e i).1.card = 1 → (e i).1 = {x}) :=
    fun i => fam_size hk (e i).2
  have hPc : ∀ i, (Finset.univ \ insert (y (e i)) (e i).1).card + (e i).1.card + 1 = 2*k := by
    intro i
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (hy1 (e i))]
    have := hsz i
    omega
  have hU : ∀ i z, z ∈ f (i,false) ∪ f (i,true) ↔ z ≠ y (e i) := by
    intro i z
    rw [hf0, hf1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro (h | ⟨_, h⟩)
      · intro hz
        rw [hz] at h
        exact hy1 (e i) h
      · intro hz
        exact h (Or.inl hz)
    · intro hz
      by_cases h : z ∈ (e i).1
      · exact Or.inl h
      · exact Or.inr ⟨Finset.mem_univ _, fun h' => h'.elim hz h⟩
  have hUc : ∀ i, (f (i,false) ∪ f (i,true)).card + 1 = 2*k := by
    intro i
    have : f (i,false) ∪ f (i,true) = Finset.univ.erase (y (e i)) := by
      ext z
      rw [hU, Finset.mem_erase]
      simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hR : ∀ i, Finset.univ \ (f (i,false) ∪ f (i,true)) = {y (e i)} := by
    intro i
    ext z
    rw [Finset.mem_sdiff, hU, Finset.mem_singleton]
    simp
  have hfc : ∀ a, 1 ≤ (f a).card ∧ (f a).card + 2 ≤ 2*k ∧ ((f a).card = 1 → f a = {x}) := by
    rintro ⟨i, b⟩
    cases b
    · rw [hf0]
      have := hsz i
      exact ⟨this.1, by omega, this.2.2⟩
    · rw [hf1]
      have := hPc i
      have := hsz i
      exact ⟨by omega, by omega, fun h => by exfalso; omega⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, b⟩ ⟨i', b'⟩ h
    cases b <;> cases b'
    · rw [hf0, hf0] at h
      have := he (Subtype.ext h)
      rw [this]
    · rw [hf0, hf1] at h
      have h1 := congrArg Finset.card h
      have := hPc i'
      have := hsz i
      have := hsz i'
      omega
    · rw [hf1, hf0] at h
      have h1 := congrArg Finset.card h
      have := hPc i
      have := hsz i'
      have := hsz i
      omega
    · rw [hf1, hf1] at h
      have h2 : insert (y (e i)) (e i).1 = insert (y (e i')) (e i').1 := by
        ext z
        have := congrArg (fun A => z ∈ A) h
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, eq_iff_iff] at this
        exact not_iff_not.1 this
      rw [← hy3 (e i), ← hy3 (e i')] at h2
      have := he (hφ h2)
      rw [this]
  · intro a
    exact Finset.card_pos.1 (by have := hfc a; omega)
  · intro i
    refine ⟨?_, ?_⟩
    · rw [hf0, hf1]
      exact Finset.disjoint_left.2 (fun z hz hz2 => (Finset.mem_sdiff.1 hz2).2 (Finset.mem_insert_of_mem hz))
    · intro h
      have := (hU i (y (e i))).1 (by rw [h]; exact Finset.mem_univ _)
      exact this rfl
  · intro a i
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 := congrArg Finset.card h
      have := hfc a
      have := hUc i
      omega
    · rw [hR i] at h
      have h1 := congrArg Finset.card h
      rw [Finset.card_singleton] at h1
      have h2 := (hfc a).2.2 h1
      rw [h2] at h
      have := Finset.singleton_injective h
      exact hy2 (e i) this.symm

end PEqualNP.Outside.L_lib_1486_aux

theorem PEqualNP.Outside.L_lib_1486 : (∀ (k m : Nat), 4 ≤ k →
  let t := 2*k
m ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + 1 →
  ∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ a i, let u := f (i,false) ∪ f (i,true)
      f a ≠ u ∧ f a ≠ Finset.univ \ u) := by
  intro k m hk t hm
  exact PEqualNP.Outside.L_lib_1486_aux.main_aux k m hk hm
