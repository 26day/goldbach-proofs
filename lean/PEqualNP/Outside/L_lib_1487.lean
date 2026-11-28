import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_1487

private lemma choose_two_mul_ge_linear (n : ℕ) (hn : 5 ≤ n) :
    (n + 1) * (4 * n + 2) ≤ Nat.choose (2 * n) n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : 2 * Nat.choose (2 * m) m ≤ Nat.choose (2 * (m + 1)) (m + 1) := by
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h1, Nat.choose_succ_succ, Nat.choose_succ_succ]
      have h3 : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m :=
        Nat.choose_le_choose m (by omega)
      omega
    have hsq : 5 * m ≤ m * m := Nat.mul_le_mul_right m hm
    have hlin : (m + 1 + 1) * (4 * (m + 1) + 2) ≤ 2 * ((m + 1) * (4 * m + 2)) := by
      have hL : (m + 1 + 1) * (4 * (m + 1) + 2) = 4 * (m * m) + 14 * m + 12 := by ring
      have hR : 2 * ((m + 1) * (4 * m + 2)) = 8 * (m * m) + 12 * m + 4 := by ring
      omega
    exact le_trans hlin (le_trans (Nat.mul_le_mul_left 2 ih) hstep)

private lemma catalan_ge_linear (k : ℕ) (hk : 6 ≤ k) :
    4 * k - 2 + Nat.choose (2 * k - 2) k ≤ Nat.choose (2 * k - 2) (k - 1) := by
  set n := k - 1 with hn_def
  have hn : 5 ≤ n := by omega
  have h2n : 2 * k - 2 = 2 * n := by omega
  have hk_eq : k = n + 1 := by omega
  rw [h2n, hk_eq]
  have hrel : Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at h
    exact h
  have hbound := choose_two_mul_ge_linear n hn
  have hmul : (n + 1) * (4 * (n + 1) - 2 + Nat.choose (2 * n) (n + 1)) ≤
      (n + 1) * Nat.choose (2 * n) n := by
    have h4 : 4 * (n + 1) - 2 = 4 * n + 2 := by omega
    rw [h4, Nat.mul_add, Nat.mul_comm (n + 1) (Nat.choose (2 * n) (n + 1)), hrel]
    have hsplit : (n + 1) * Nat.choose (2 * n) n =
        Nat.choose (2 * n) n + Nat.choose (2 * n) n * n := by ring
    omega
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

private lemma table_k4 (q : ℕ) (hq1 : 2 ≤ q) (hq2 : q ≤ 8) :
    2 * (q - 1) ≤ ∑ j ∈ Finset.range 4,
      (Nat.choose q j * Nat.choose (8 - q) (3 - j) -
       Nat.choose q j * Nat.choose (8 - q) (4 - j)) := by
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Finset.sum_range_succ, Nat.choose]

private lemma table_k5 (q : ℕ) (hq1 : 2 ≤ q) (hq2 : q ≤ 10) :
    2 * (q - 1) ≤ ∑ j ∈ Finset.range 5,
      (Nat.choose q j * Nat.choose (10 - q) (4 - j) -
       Nat.choose q j * Nat.choose (10 - q) (5 - j)) := by
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Finset.sum_range_succ, Nat.choose]

private lemma card_filter_card_inter {t : ℕ} (Q : Finset (Fin t)) (r j : ℕ) (hjr : j ≤ r) :
    ((Finset.univ : Finset (Finset (Fin t))).filter (fun A => A.card = r ∧ (A ∩ Q).card = j)).card =
      Nat.choose Q.card j * Nat.choose (t - Q.card) (r - j) := by
  have hbij : ((Q.powersetCard j) ×ˢ ((Finset.univ \ Q).powersetCard (r - j))).card =
      ((Finset.univ : Finset (Finset (Fin t))).filter (fun A => A.card = r ∧ (A ∩ Q).card = j)).card := by
    refine Finset.card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rcases Finset.mem_powersetCard.mp hp1 with ⟨h1sub, h1card⟩
      rcases Finset.mem_powersetCard.mp hp2 with ⟨h2sub, h2card⟩
      have hdisj : Disjoint p.1 p.2 := Finset.disjoint_left.mpr fun x hx1 hx2 =>
        (Finset.mem_sdiff.mp (h2sub hx2)).2 (h1sub hx1)
      have hinter : (p.1 ∪ p.2) ∩ Q = p.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx1 | hx2, hxQ⟩
          · exact hx1
          · exact absurd hxQ (Finset.mem_sdiff.mp (h2sub hx2)).2
        · intro hx1
          exact ⟨Or.inl hx1, h1sub hx1⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, h1card, h2card]; omega
      · rw [hinter, h1card]
    · intro p1 hp1 p2 hp2 heq
      rcases Finset.mem_product.mp hp1 with ⟨h1a, h1b⟩
      rcases Finset.mem_product.mp hp2 with ⟨h2a, h2b⟩
      have h1a_sub := (Finset.mem_powersetCard.mp h1a).1
      have h1b_sub := (Finset.mem_powersetCard.mp h1b).1
      have h2a_sub := (Finset.mem_powersetCard.mp h2a).1
      have h2b_sub := (Finset.mem_powersetCard.mp h2b).1
      have hfst : p1.1 = p2.1 := by
        ext x
        have hx := Finset.ext_iff.mp heq x
        simp only [Finset.mem_union] at hx
        constructor
        · intro h
          rcases hx.mp (Or.inl h) with h' | h'
          · exact h'
          · exact absurd (h1a_sub h) (Finset.mem_sdiff.mp (h2b_sub h')).2
        · intro h
          rcases hx.mpr (Or.inl h) with h' | h'
          · exact h'
          · exact absurd (h2a_sub h) (Finset.mem_sdiff.mp (h1b_sub h')).2
      have hsnd : p1.2 = p2.2 := by
        ext x
        have hx := Finset.ext_iff.mp heq x
        simp only [Finset.mem_union] at hx
        constructor
        · intro h
          rcases hx.mp (Or.inr h) with h' | h'
          · exact absurd (h2a_sub h') (Finset.mem_sdiff.mp (h1b_sub h)).2
          · exact h'
        · intro h
          rcases hx.mpr (Or.inr h) with h' | h'
          · exact absurd (h1a_sub h') (Finset.mem_sdiff.mp (h2b_sub h)).2
          · exact h'
      exact Prod.ext hfst hsnd
    · intro A hA
      rcases (Finset.mem_filter.mp hA).2 with ⟨hAcard, hAQcard⟩
      refine ⟨(A ∩ Q, A \ Q), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hAQcard⟩
      · refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
        · dsimp only
          have h := Finset.card_sdiff_add_card_inter A Q
          omega
      · rw [Finset.union_comm]; exact Finset.sdiff_union_inter A Q
  rw [← hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ Q), Finset.card_univ, Fintype.card_fin]

private lemma card_avoid_two {t : ℕ} (a b : Fin t) (hab : a ≠ b) (r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin t))).filter (fun A => A.card = r ∧ a ∉ A ∧ b ∉ A)).card =
      Nat.choose (t - 2) r := by
  have heq : (Finset.univ : Finset (Finset (Fin t))).filter (fun A => A.card = r ∧ a ∉ A ∧ b ∉ A) =
      (Finset.univ \ ({a, b} : Finset (Fin t))).powersetCard r := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_iff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨hcard, ha, hb⟩
      exact ⟨fun x hx => ⟨fun hxa => ha (hxa ▸ hx), fun hxb => hb (hxb ▸ hx)⟩, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨hcard, fun ha => (hsub ha).1 rfl, fun hb => (hsub hb).2 rfl⟩
  rw [heq, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, Finset.card_pair hab]

open scoped Classical in
private lemma main_proof : (∀ (k m : Nat), 4 ≤ k →
  let t := 2*k
  (∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ a i, let u := f (i,false) ∪ f (i,true)
      f a ≠ u ∧ f a ≠ Finset.univ \ u) →
  m ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + 1) := by
  intro k m hk t ⟨f, hf_inj, hf_ne, hf_pair, hf_avoid⟩
  let u : Fin m → Finset (Fin t) := fun i => f (i, false) ∪ f (i, true)
  let r : Fin m → Finset (Fin t) := fun i => Finset.univ \ u i
  have hcard_pair : ∀ i : Fin m, (f (i, false)).card + (f (i, true)).card + (r i).card = t := by
    intro i
    have h1 : (u i).card + (r i).card = t := by
      have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin t)) (u i)
      rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
      change (u i).card + (Finset.univ \ u i).card = t
      omega
    have h2 : (u i).card = (f (i, false)).card + (f (i, true)).card :=
      Finset.card_union_of_disjoint (hf_pair i).1
    omega
  have hr_pos : ∀ i : Fin m, 1 ≤ (r i).card := by
    intro i
    have hne : (r i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      apply (hf_pair i).2
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hmem : x ∈ r i := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hemp] at hmem
      simp at hmem
    exact Finset.Nonempty.card_pos hne
  let Q : Finset (Fin t) := Finset.univ.filter (fun x => ∀ i : Fin m, r i ≠ {x})
  let q := Q.card
  have hq_le : q ≤ t := by
    calc q = Q.card := rfl
      _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_card (Finset.subset_univ Q)
      _ = t := by rw [Finset.card_univ, Fintype.card_fin]
  let S_all : Finset (Finset (Fin t)) :=
    Finset.univ.filter (fun A => 2 ≤ A.card ∧ A.card < k)
  let S_one : Finset (Finset (Fin t)) := Q.image (fun x => ({x} : Finset (Fin t)))
  let Small : Finset (Finset (Fin t)) := S_all ∪ S_one
  have hS_all_card : S_all.card = ∑ j ∈ Finset.Ico 2 k, Nat.choose t j := by
    have heq : S_all = (Finset.Ico 2 k).biUnion (fun j => (Finset.univ : Finset (Fin t)).powersetCard j) := by
      ext A
      simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_Ico, Finset.mem_powersetCard, Finset.subset_univ]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨A.card, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨j, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    rw [heq, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    · intro j1 _ j2 _ hne
      refine Finset.disjoint_left.mpr fun A h1 h2 => ?_
      have c1 := (Finset.mem_powersetCard.mp h1).2
      have c2 := (Finset.mem_powersetCard.mp h2).2
      exact hne (c1.symm.trans c2)
  have hS_one_card : S_one.card = q := by
    rw [Finset.card_image_of_injective _ (fun x y h => Finset.singleton_injective h)]
  have hS_disj : Disjoint S_all S_one := by
    refine Finset.disjoint_left.mpr fun A h1 h2 => ?_
    have c1 := (Finset.mem_filter.mp h1).2.1
    rcases Finset.mem_image.mp h2 with ⟨x, _, rfl⟩
    simp at c1
  have hSmall_card : Small.card = (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + q := by
    rw [Finset.card_union_of_disjoint hS_disj, hS_all_card, hS_one_card]
  have hmem_small : ∀ a : Fin m × Bool, f a ∈ Small ↔ (f a).card < k := by
    intro a
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · exact (Finset.mem_filter.mp h1).2.2
      · rcases Finset.mem_image.mp h2 with ⟨x, _, hx⟩
        rw [← hx, Finset.card_singleton]; omega
    · intro hlt
      have hpos : 1 ≤ (f a).card := Finset.Nonempty.card_pos (hf_ne a)
      by_cases h1 : (f a).card = 1
      · apply Finset.mem_union_right
        rcases Finset.card_eq_one.mp h1 with ⟨x, hx⟩
        refine Finset.mem_image.mpr ⟨x, ?_, hx.symm⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun i hri => ?_⟩
        exact (hf_avoid a i).2 (hx.trans hri.symm)
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hlt⟩
  let D : Finset (Fin m) :=
    Finset.univ.filter (fun i => (f (i, false)).card < k ∧ (f (i, true)).card < k)
  let Used : Finset (Finset (Fin t)) := (Finset.univ.image f) ∩ Small
  let Unused : Finset (Finset (Fin t)) := Small \ Used
  have hUsed_card : Used.card = m + D.card := by
    have h1 : Used = (Finset.univ.filter (fun a : Fin m × Bool => f a ∈ Small)).image f := by
      ext A
      simp only [Used, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · rintro ⟨⟨a, rfl⟩, hsm⟩; exact ⟨a, hsm, rfl⟩
      · rintro ⟨a, hsm, rfl⟩; exact ⟨⟨a, rfl⟩, hsm⟩
    rw [h1, Finset.card_image_of_injective _ hf_inj, Finset.card_filter]
    rw [Fintype.sum_prod_type]
    have hsum : ∑ i : Fin m, ∑ b : Bool, (if f (i, b) ∈ Small then 1 else 0) =
        ∑ i : Fin m, (1 + if i ∈ D then 1 else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_bool]
      simp only [hmem_small, D, Finset.mem_filter, Finset.mem_univ, true_and]
      have hcp := hcard_pair i
      have hrp := hr_pos i
      by_cases hf0 : (f (i, false)).card < k <;> by_cases hf1 : (f (i, true)).card < k
      · simp [hf0, hf1]
      · simp [hf0, hf1]
      · simp [hf0, hf1]
      · omega
    rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.card_filter]
    simp
  have hbalance : (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + q = m + D.card + Unused.card := by
    have h := Finset.card_sdiff_add_card_inter Small Used
    have hinter : Small ∩ Used = Used := Finset.inter_eq_right.mpr Finset.inter_subset_right
    rw [hinter] at h
    change (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + q = m + D.card + (Small \ Used).card
    rw [← hSmall_card, ← h, hUsed_card]
    omega
  by_cases hq1 : q ≤ 1
  · omega
  have hq2 : 2 ≤ q := by omega
  let Case3 : Finset (Finset (Fin t)) :=
    Finset.univ.filter (fun A => A.card = k - 1 ∧ ∃ i : Fin m, ∃ b : Bool, f (i, b) = A ∧ i ∉ D)
  let Bad : Finset (Finset (Fin t)) :=
    Finset.univ.filter (fun A => A.card = k - 1 ∧ A ∉ Case3)
  have hBad_le : Bad.card ≤ 2 * (Unused.card + D.card) := by
    have hsplit : Bad.card = (Bad ∩ Unused).card + (Bad ∩ Used).card := by
      have hsub : Bad ⊆ Small := by
        intro A hA
        apply Finset.mem_union_left
        have hc := (Finset.mem_filter.mp hA).2.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, by omega, by omega⟩
      have heq : Bad = (Bad ∩ Unused) ∪ (Bad ∩ Used) := by
        ext A
        simp only [Finset.mem_union, Finset.mem_inter, Unused, Finset.mem_sdiff]
        constructor
        · intro hA
          by_cases hu : A ∈ Used
          · exact Or.inr ⟨hA, hu⟩
          · exact Or.inl ⟨hA, hsub hA, hu⟩
        · rintro (⟨hA, _⟩ | ⟨hA, _⟩) <;> exact hA
      have hdisj : Disjoint (Bad ∩ Unused) (Bad ∩ Used) :=
        Finset.disjoint_left.mpr fun A h1 h2 =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).2 (Finset.mem_inter.mp h2).2
      conv_lhs => rw [heq]
      rw [Finset.card_union_of_disjoint hdisj]
    have h1 : (Bad ∩ Unused).card ≤ Unused.card := Finset.card_le_card Finset.inter_subset_right
    have h2 : (Bad ∩ Used).card ≤ 2 * D.card := by
      have hsub : Bad ∩ Used ⊆ (D ×ˢ (Finset.univ : Finset Bool)).image f := by
        intro A hA
        rcases Finset.mem_inter.mp hA with ⟨hBad, hUsed⟩
        rcases Finset.mem_filter.mp hBad with ⟨_, hc, hnot3⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hUsed).1 with ⟨⟨i, b⟩, _, rfl⟩
        have hiD : i ∈ D := by
          by_contra hi
          exact hnot3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, i, b, rfl, hi⟩)
        exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_product.mpr ⟨hiD, Finset.mem_univ b⟩, rfl⟩
      calc (Bad ∩ Used).card ≤ ((D ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ (D ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = 2 * D.card := by rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; omega
    omega
  have hCase3_prop : ∀ A ∈ Case3, ∃ (i : Fin m) (b : Bool),
      f (i, b) = A ∧ (f (i, !b)).card = k ∧ (Finset.univ \ f (i, !b)).card = k ∧
      (Finset.univ \ f (i, !b)) ∩ Q = A ∩ Q := by
    intro A hA
    rcases (Finset.mem_filter.mp hA).2 with ⟨hAcard, i, b, hfab, hiD⟩
    have hfab_card : (f (i, b)).card = k - 1 := by rw [hfab]; exact hAcard
    have hpart_ge : k ≤ (f (i, !b)).card := by
      by_contra hlt
      apply hiD
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_, ?_⟩
      · cases b <;> simp_all <;> omega
      · cases b <;> simp_all <;> omega
    have hsum_ab : (f (i, b)).card + (f (i, !b)).card + (r i).card = t := by
      have h := hcard_pair i
      cases b <;> simp only [Bool.not_false, Bool.not_true] at * <;> omega
    have hr1 : (r i).card = 1 := by have := hr_pos i; omega
    have hpcard : (f (i, !b)).card = k := by omega
    rcases Finset.card_eq_one.mp hr1 with ⟨x, hrx⟩
    have hxQ : x ∉ Q := by
      intro hmem
      exact (Finset.mem_filter.mp hmem).2 i hrx
    have hdisj_ab : Disjoint (f (i, b)) (f (i, !b)) := by
      cases b
      · exact (hf_pair i).1
      · exact (hf_pair i).1.symm
    have hunion_ab : f (i, b) ∪ f (i, !b) = u i := by
      cases b
      · rfl
      · exact Finset.union_comm _ _
    have hE_eq : Finset.univ \ f (i, !b) = A ∪ {x} := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton]
      rw [← hfab]
      constructor
      · intro hy
        by_cases hyu : y ∈ u i
        · rw [← hunion_ab] at hyu
          rcases Finset.mem_union.mp hyu with h1 | h2
          · exact Or.inl h1
          · exact absurd h2 hy
        · have hyr : y ∈ r i := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyu⟩
          rw [hrx, Finset.mem_singleton] at hyr
          exact Or.inr hyr
      · rintro (h1 | hyx)
        · exact Finset.disjoint_left.mp hdisj_ab h1
        · intro hx2
          subst hyx
          have hxu : y ∈ u i := by rw [← hunion_ab]; exact Finset.mem_union_right _ hx2
          have hxr : y ∈ r i := by rw [hrx]; exact Finset.mem_singleton_self y
          exact (Finset.mem_sdiff.mp hxr).2 hxu
    refine ⟨i, b, hfab, hpcard, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        hpcard]
      omega
    · rw [hE_eq]
      ext y
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | rfl, hyQ⟩
        · exact ⟨h1, hyQ⟩
        · exact absurd hyQ hxQ
      · rintro ⟨h1, hyQ⟩
        exact ⟨Or.inl h1, hyQ⟩
  let φ : Finset (Fin t) → Finset (Fin t) := fun A =>
    if hA : A ∈ Case3 then
      let i := (hCase3_prop A hA).choose
      let b := (hCase3_prop A hA).choose_spec.choose
      Finset.univ \ f (i, !b)
    else ∅
  have hφ_card : ∀ A ∈ Case3, (φ A).card = k := by
    intro A hA
    simp only [φ, hA, ↓reduceDIte]
    exact (hCase3_prop A hA).choose_spec.choose_spec.2.2.1
  have hφ_inter : ∀ A ∈ Case3, (φ A) ∩ Q = A ∩ Q := by
    intro A hA
    simp only [φ, hA, ↓reduceDIte]
    exact (hCase3_prop A hA).choose_spec.choose_spec.2.2.2
  have hφ_inj : Set.InjOn φ (Case3 : Set (Finset (Fin t))) := by
    intro A1 hA1 A2 hA2 heq
    have hA1' : A1 ∈ Case3 := hA1
    have hA2' : A2 ∈ Case3 := hA2
    simp only [φ, hA1', hA2', ↓reduceDIte] at heq
    let i1 := (hCase3_prop A1 hA1').choose
    let b1 := (hCase3_prop A1 hA1').choose_spec.choose
    let i2 := (hCase3_prop A2 hA2').choose
    let b2 := (hCase3_prop A2 hA2').choose_spec.choose
    have h1 : f (i1, b1) = A1 := (hCase3_prop A1 hA1').choose_spec.choose_spec.1
    have h2 : f (i2, b2) = A2 := (hCase3_prop A2 hA2').choose_spec.choose_spec.1
    have hfeq : f (i1, !b1) = f (i2, !b2) := by
      ext y
      have hy := Finset.ext_iff.mp heq y
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hy
      exact not_iff_not.mp hy
    have hp := hf_inj hfeq
    have hi : i1 = i2 := congrArg Prod.fst hp
    have hb : (!b1) = (!b2) := congrArg Prod.snd hp
    have hb' : b1 = b2 := by rw [← Bool.not_not b1, ← Bool.not_not b2, hb]
    rw [← h1, ← h2, hi, hb']
  suffices hloss : 2 * (q - 1) ≤ Bad.card by omega
  by_cases hk6 : 6 ≤ k
  · have hQ2 : 1 < Q.card := by omega
    rcases Finset.one_lt_card.mp hQ2 with ⟨a, haQ, b, hbQ, hab⟩
    let L : Finset (Finset (Fin t)) :=
      Finset.univ.filter (fun A => A.card = k - 1 ∧ a ∉ A ∧ b ∉ A)
    let R : Finset (Finset (Fin t)) :=
      Finset.univ.filter (fun E => E.card = k ∧ a ∉ E ∧ b ∉ E)
    have hL_le : L.card ≤ R.card + Bad.card := by
      have hpart : L.card = (L ∩ Case3).card + (L \ Case3).card := by
        have h := Finset.card_sdiff_add_card_inter L Case3
        omega
      have h1 : (L ∩ Case3).card ≤ R.card := by
        refine Finset.card_le_card_of_injOn φ ?_ ?_
        · intro A hA
          rcases Finset.mem_inter.mp hA with ⟨hAL, hAC3⟩
          rcases (Finset.mem_filter.mp hAL).2 with ⟨_, haA, hbA⟩
          have hint := hφ_inter A hAC3
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_card A hAC3, ?_, ?_⟩
          · intro ha
            have : a ∈ (φ A) ∩ Q := Finset.mem_inter.mpr ⟨ha, haQ⟩
            rw [hint] at this
            exact haA (Finset.mem_inter.mp this).1
          · intro hb
            have : b ∈ (φ A) ∩ Q := Finset.mem_inter.mpr ⟨hb, hbQ⟩
            rw [hint] at this
            exact hbA (Finset.mem_inter.mp this).1
        · exact hφ_inj.mono (by intro A hA; exact (Finset.mem_inter.mp hA).2)
      have h2 : (L \ Case3).card ≤ Bad.card := by
        refine Finset.card_le_card fun A hA => ?_
        rcases Finset.mem_sdiff.mp hA with ⟨hAL, hnot3⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, (Finset.mem_filter.mp hAL).2.1, hnot3⟩
      omega
    have hL_card : L.card = Nat.choose (2 * k - 2) (k - 1) := card_avoid_two a b hab (k - 1)
    have hR_card : R.card = Nat.choose (2 * k - 2) k := card_avoid_two a b hab k
    have hcat := catalan_ge_linear k hk6
    omega
  · let L : ℕ → Finset (Finset (Fin t)) := fun j =>
      Finset.univ.filter (fun A => A.card = k - 1 ∧ (A ∩ Q).card = j)
    let R : ℕ → Finset (Finset (Fin t)) := fun j =>
      Finset.univ.filter (fun E => E.card = k ∧ (E ∩ Q).card = j)
    have hshort : ∀ j ∈ Finset.range k, (L j).card - (R j).card ≤ (L j ∩ Bad).card := by
      intro j _
      have hpart : (L j).card = (L j ∩ Case3).card + (L j \ Case3).card := by
        have h := Finset.card_sdiff_add_card_inter (L j) Case3
        omega
      have h1 : (L j ∩ Case3).card ≤ (R j).card := by
        refine Finset.card_le_card_of_injOn φ ?_ ?_
        · intro A hA
          rcases Finset.mem_inter.mp hA with ⟨hAL, hAC3⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_card A hAC3, ?_⟩
          rw [hφ_inter A hAC3]
          exact (Finset.mem_filter.mp hAL).2.2
        · exact hφ_inj.mono (by intro A hA; exact (Finset.mem_inter.mp hA).2)
      have h2 : L j \ Case3 ⊆ L j ∩ Bad := by
        intro A hA
        rcases Finset.mem_sdiff.mp hA with ⟨hAL, hnot3⟩
        exact Finset.mem_inter.mpr ⟨hAL, Finset.mem_filter.mpr
          ⟨Finset.mem_univ A, (Finset.mem_filter.mp hAL).2.1, hnot3⟩⟩
      have h2c := Finset.card_le_card h2
      omega
    have hsum_le_Bad : ∑ j ∈ Finset.range k, ((L j).card - (R j).card) ≤ Bad.card := by
      calc ∑ j ∈ Finset.range k, ((L j).card - (R j).card)
          ≤ ∑ j ∈ Finset.range k, (L j ∩ Bad).card := Finset.sum_le_sum hshort
        _ = ((Finset.range k).biUnion (fun j => L j ∩ Bad)).card := by
            symm
            refine Finset.card_biUnion fun j1 _ j2 _ hne => ?_
            refine Finset.disjoint_left.mpr fun A h1 h2 => ?_
            have c1 := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).1).2.2
            have c2 := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).1).2.2
            exact hne (c1.symm.trans c2)
        _ ≤ Bad.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => Finset.inter_subset_right)
    have hsum_eq : ∑ j ∈ Finset.range k, ((L j).card - (R j).card) =
        ∑ j ∈ Finset.range k,
          (Nat.choose q j * Nat.choose (2 * k - q) (k - 1 - j) -
           Nat.choose q j * Nat.choose (2 * k - q) (k - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < k := Finset.mem_range.mp hj
      rw [card_filter_card_inter Q (k - 1) j (by omega), card_filter_card_inter Q k j (by omega)]
    rw [hsum_eq] at hsum_le_Bad
    have hk45 : k = 4 ∨ k = 5 := by omega
    rcases hk45 with rfl | rfl
    · exact le_trans (table_k4 q hq2 hq_le) hsum_le_Bad
    · exact le_trans (table_k5 q hq2 hq_le) hsum_le_Bad

end PEqualNP.Outside.L_lib_1487

theorem PEqualNP.Outside.L_lib_1487 : (∀ (k m : Nat), 4 ≤ k →
  let t := 2*k
  (∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ a i, let u := f (i,false) ∪ f (i,true)
      f a ≠ u ∧ f a ≠ Finset.univ \ u) →
  m ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + 1) :=
  PEqualNP.Outside.L_lib_1487.main_proof
