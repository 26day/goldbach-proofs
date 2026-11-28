import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1491.P1b

open Finset

theorem core {k m : ℕ} (S : Fin k → Finset (Fin m)) (hS : ∀ j, (S j).card ≤ 2) :
    ∀ n : ℕ, ∀ (P Q : Finset (Fin k)) (D : Finset (Fin m)), P.card = n → Q.card < P.card →
      (∀ c ∈ D, ∃ p ∈ P, c ∈ S p) → (∀ c ∈ D, ∃ q ∈ Q, c ∈ S q) →
      ∃ T U : Finset (Fin k), T ⊆ P ∧ U ⊆ Q ∧ T.card = U.card + 1 ∧
        (∀ c ∈ D, ∃ j ∈ (P \ T) ∪ U, c ∈ S j) ∧ (∀ c ∈ D, ∃ j ∈ (Q \ U) ∪ T, c ∈ S j) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q D hPn hlt hP hQ

  by_cases hA : ∃ p ∈ P, ∀ c ∈ D, ∃ p' ∈ P.erase p, c ∈ S p'
  · obtain ⟨p, hp, hcov⟩ := hA
    refine ⟨{p}, ∅, by simpa using hp, empty_subset _, by simp, ?_, ?_⟩
    · intro c hc
      obtain ⟨p', hp', hc'⟩ := hcov c hc
      refine ⟨p', ?_, hc'⟩
      rw [mem_erase] at hp'
      simp [hp'.1, hp'.2]
    · intro c hc
      obtain ⟨q, hq, hc'⟩ := hQ c hc
      exact ⟨q, by simp [hq], hc'⟩

  by_cases hB : ∃ p ∈ P, ∃ c ∈ D, c ∈ S p ∧
      ∀ c' ∈ D, c' ∈ S p → c' ≠ c → ∃ p' ∈ P.erase p, c' ∈ S p'
  · obtain ⟨p, hp, c, hcD, hcp, hrest⟩ := hB
    obtain ⟨q, hq, hcq⟩ := hQ c hcD
    have hP' : ∀ d ∈ D \ S q, ∃ p' ∈ P.erase p, d ∈ S p' := by
      intro d hd
      rw [mem_sdiff] at hd
      obtain ⟨p0, hp0, hd0⟩ := hP d hd.1
      by_cases h0 : p0 = p
      · subst h0
        exact hrest d hd.1 hd0 (fun h => hd.2 (h ▸ hcq))
      · exact ⟨p0, mem_erase.2 ⟨h0, hp0⟩, hd0⟩
    have hQ' : ∀ d ∈ D \ S q, ∃ q' ∈ Q.erase q, d ∈ S q' := by
      intro d hd
      rw [mem_sdiff] at hd
      obtain ⟨q0, hq0, hd0⟩ := hQ d hd.1
      refine ⟨q0, mem_erase.2 ⟨?_, hq0⟩, hd0⟩
      rintro rfl
      exact hd.2 hd0
    have hPc : (P.erase p).card = P.card - 1 := card_erase_of_mem hp
    have hQc : (Q.erase q).card = Q.card - 1 := card_erase_of_mem hq
    have hQpos : 0 < Q.card := card_pos.2 ⟨q, hq⟩
    obtain ⟨T', U', hT', hU', hcard, hc1, hc2⟩ :=
      ih (P.card - 1) (by omega) (P.erase p) (Q.erase q) (D \ S q) hPc (by omega) hP' hQ'
    have hpT' : p ∉ T' := fun h => by simpa using hT' h
    have hqU' : q ∉ U' := fun h => by simpa using hU' h
    by_cases hopt : ∀ d ∈ D, d ∈ S q → d ≠ c → ∃ j ∈ P \ T', d ∈ S j
    ·
      refine ⟨T', U', hT'.trans (erase_subset _ _), hU'.trans (erase_subset _ _), hcard, ?_, ?_⟩
      · intro d hd
        by_cases hdq : d ∈ S q
        · by_cases hdc : d = c
          · subst hdc
            exact ⟨p, by simp [hp, hpT'], hcp⟩
          · obtain ⟨j, hj, hdj⟩ := hopt d hd hdq hdc
            exact ⟨j, mem_union_left _ hj, hdj⟩
        · obtain ⟨j, hj, hdj⟩ := hc1 d (mem_sdiff.2 ⟨hd, hdq⟩)
          refine ⟨j, ?_, hdj⟩
          simp only [mem_union, mem_sdiff, mem_erase] at hj ⊢
          tauto
      · intro d hd
        by_cases hdq : d ∈ S q
        · exact ⟨q, by simp [hq, hqU'], hdq⟩
        · obtain ⟨j, hj, hdj⟩ := hc2 d (mem_sdiff.2 ⟨hd, hdq⟩)
          refine ⟨j, ?_, hdj⟩
          simp only [mem_union, mem_sdiff, mem_erase] at hj ⊢
          tauto
    ·
      push Not at hopt
      obtain ⟨d0, hd0D, hd0q, hd0c, hd0none⟩ := hopt
      refine ⟨insert p T', insert q U', ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · exact hp
        · exact mem_of_mem_erase (hT' hx)
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · exact hq
        · exact mem_of_mem_erase (hU' hx)
      · rw [card_insert_of_notMem hpT', card_insert_of_notMem hqU', hcard]
      · intro d hd
        by_cases hdq : d ∈ S q
        · exact ⟨q, by simp, hdq⟩
        · obtain ⟨j, hj, hdj⟩ := hc1 d (mem_sdiff.2 ⟨hd, hdq⟩)
          refine ⟨j, ?_, hdj⟩
          simp only [mem_union, mem_sdiff, mem_erase, mem_insert] at hj ⊢
          tauto
      · intro d hd
        by_cases hdq : d ∈ S q
        · by_cases hdc : d = c
          · subst hdc
            exact ⟨p, by simp, hcp⟩
          · have hdd0 : d = d0 := by
              by_contra hne
              have h3 : 2 < (S q).card :=
                two_lt_card.2 ⟨c, hcq, d, hdq, d0, hd0q, Ne.symm hdc, Ne.symm hd0c, hne⟩
              have := hS q
              omega
            subst hdd0
            obtain ⟨p0, hp0, hdp0⟩ := hP d hd
            have hp0T : p0 ∈ T' := by
              by_contra hn
              exact hd0none p0 (mem_sdiff.2 ⟨hp0, hn⟩) hdp0
            exact ⟨p0, by simp [hp0T], hdp0⟩
        · obtain ⟨j, hj, hdj⟩ := hc2 d (mem_sdiff.2 ⟨hd, hdq⟩)
          refine ⟨j, ?_, hdj⟩
          simp only [mem_union, mem_sdiff, mem_erase, mem_insert] at hj ⊢
          tauto

  exfalso
  push Not at hA hB
  set priv : Fin k → Finset (Fin m) :=
    fun p => D.filter (fun c => c ∈ S p ∧ ∀ p' ∈ P.erase p, c ∉ S p') with hpriv
  have h2 : ∀ p ∈ P, 2 ≤ (priv p).card := by
    intro p hp
    obtain ⟨c, hcD, hc⟩ := hA p hp
    have hcp : c ∈ S p := by
      obtain ⟨p0, hp0, h0⟩ := hP c hcD
      by_cases h : p0 = p
      · subst h
        exact h0
      · exact absurd h0 (hc p0 (mem_erase.2 ⟨h, hp0⟩))
    obtain ⟨c', hc'D, hc'p, hc'c, hc'⟩ := hB p hp c hcD hcp
    have hsub : ({c, c'} : Finset (Fin m)) ⊆ priv p := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter.2 ⟨hcD, hcp, hc⟩
      · exact mem_filter.2 ⟨hc'D, hc'p, hc'⟩
    have := card_le_card hsub
    rw [card_pair (Ne.symm hc'c)] at this
    exact this
  have hdisj : (P : Set (Fin k)).PairwiseDisjoint priv := by
    intro p hp p' hp' hne
    rw [Function.onFun, disjoint_left]
    intro c hc hc'
    rw [hpriv, mem_filter] at hc hc'
    exact hc'.2.2 p (mem_erase.2 ⟨hne, hp⟩) hc.2.1
  have hsub : P.biUnion priv ⊆ D := biUnion_subset.2 (fun p _ => filter_subset _ _)
  have hsum : 2 * P.card ≤ ∑ p ∈ P, (priv p).card := by
    calc 2 * P.card = ∑ _p ∈ P, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ P, (priv p).card := sum_le_sum h2
  have hcardP : (P.biUnion priv).card = ∑ p ∈ P, (priv p).card := card_biUnion hdisj
  have hDQ : D ⊆ Q.biUnion S := by
    intro c hc
    obtain ⟨q, hq, hcq⟩ := hQ c hc
    exact mem_biUnion.2 ⟨q, hq, hcq⟩
  have hD : D.card ≤ 2 * Q.card := by
    calc D.card ≤ (Q.biUnion S).card := card_le_card hDQ
      _ ≤ ∑ q ∈ Q, (S q).card := card_biUnion_le
      _ ≤ ∑ _q ∈ Q, 2 := sum_le_sum (fun q _ => hS q)
      _ = 2 * Q.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have := card_le_card hsub
  omega

theorem step {k m : ℕ} (S : Fin k → Finset (Fin m)) (hS : ∀ j, (S j).card ≤ 2)
    (A B : Finset (Fin k)) (hA : A.biUnion S = univ) (hB : B.biUnion S = univ)
    (hlt : B.card + 1 < A.card) :
    ∃ A' B' : Finset (Fin k), A'.biUnion S = univ ∧ B'.biUnion S = univ ∧
      (∀ j, (j ∈ A' ∧ j ∈ B' ↔ j ∈ A ∧ j ∈ B)) ∧ (∀ j, (j ∈ A' ∨ j ∈ B' ↔ j ∈ A ∨ j ∈ B)) ∧
      A'.card + 1 = A.card ∧ B'.card = B.card + 1 := by
  classical
  set D : Finset (Fin m) := univ.filter (fun c => ∀ j ∈ A ∩ B, c ∉ S j) with hDdef
  have hPD : ∀ c ∈ D, ∃ p ∈ A \ B, c ∈ S p := by
    intro c hc
    rw [hDdef, mem_filter] at hc
    have : c ∈ A.biUnion S := hA ▸ mem_univ c
    obtain ⟨j, hj, hcj⟩ := mem_biUnion.1 this
    exact ⟨j, mem_sdiff.2 ⟨hj, fun hjB => hc.2 j (mem_inter.2 ⟨hj, hjB⟩) hcj⟩, hcj⟩
  have hQD : ∀ c ∈ D, ∃ q ∈ B \ A, c ∈ S q := by
    intro c hc
    rw [hDdef, mem_filter] at hc
    have : c ∈ B.biUnion S := hB ▸ mem_univ c
    obtain ⟨j, hj, hcj⟩ := mem_biUnion.1 this
    exact ⟨j, mem_sdiff.2 ⟨hj, fun hjA => hc.2 j (mem_inter.2 ⟨hjA, hj⟩) hcj⟩, hcj⟩
  have hcard : (B \ A).card < (A \ B).card := by
    have h1 := card_sdiff_add_card_inter A B
    have h2 := card_sdiff_add_card_inter B A
    rw [inter_comm] at h2
    omega
  obtain ⟨T, U, hT, hU, hTU, hc1, hc2⟩ := core S hS _ (A \ B) (B \ A) D rfl hcard hPD hQD
  refine ⟨(A \ T) ∪ U, (B \ U) ∪ T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_univ_iff_forall]
    intro c
    rw [mem_biUnion]
    by_cases hcD : c ∈ D
    · obtain ⟨j, hj, hcj⟩ := hc1 c hcD
      refine ⟨j, ?_, hcj⟩
      simp only [mem_union, mem_sdiff] at hj ⊢
      tauto
    · rw [hDdef, mem_filter] at hcD
      simp only [mem_univ, true_and, not_forall, not_not] at hcD
      obtain ⟨j, hj, hcj⟩ := hcD
      rw [mem_inter] at hj
      exact ⟨j, mem_union_left _ (mem_sdiff.2 ⟨hj.1, fun hjT => (mem_sdiff.1 (hT hjT)).2 hj.2⟩),
        hcj⟩
  · rw [eq_univ_iff_forall]
    intro c
    rw [mem_biUnion]
    by_cases hcD : c ∈ D
    · obtain ⟨j, hj, hcj⟩ := hc2 c hcD
      refine ⟨j, ?_, hcj⟩
      simp only [mem_union, mem_sdiff] at hj ⊢
      tauto
    · rw [hDdef, mem_filter] at hcD
      simp only [mem_univ, true_and, not_forall, not_not] at hcD
      obtain ⟨j, hj, hcj⟩ := hcD
      rw [mem_inter] at hj
      exact ⟨j, mem_union_left _ (mem_sdiff.2 ⟨hj.2, fun hjU => (mem_sdiff.1 (hU hjU)).2 hj.1⟩),
        hcj⟩
  · intro j
    have h1 := @hT j
    have h2 := @hU j
    simp only [mem_union, mem_sdiff] at h1 h2 ⊢
    tauto
  · intro j
    have h1 := @hT j
    have h2 := @hU j
    simp only [mem_union, mem_sdiff] at h1 h2 ⊢
    tauto
  · have hd : Disjoint (A \ T) U := by
      rw [disjoint_left]
      intro x hx hxU
      exact (mem_sdiff.1 (hU hxU)).2 (mem_sdiff.1 hx).1
    have hTA : T ⊆ A := hT.trans sdiff_subset
    rw [card_union_of_disjoint hd, card_sdiff_of_subset hTA]
    have : T.card ≤ A.card := card_le_card hTA
    omega
  · have hd : Disjoint (B \ U) T := by
      rw [disjoint_left]
      intro x hx hxT
      exact (mem_sdiff.1 (hT hxT)).2 (mem_sdiff.1 hx).1
    have hUB : U ⊆ B := hU.trans sdiff_subset
    rw [card_union_of_disjoint hd, card_sdiff_of_subset hUB]
    have : U.card ≤ B.card := card_le_card hUB
    omega

theorem sum_two {r : ℕ} (f f' : Fin r → ℕ) (i h : Fin r) (hih : i ≠ h)
    (heq : ∀ l, l ≠ i → l ≠ h → f' l = f l) :
    (∑ l, f' l) + (f i + f h) = (∑ l, f l) + (f' i + f' h) := by
  have hh : h ∈ (univ : Finset (Fin r)).erase i := mem_erase.2 ⟨hih.symm, mem_univ h⟩
  rw [← add_sum_erase _ f' (mem_univ i), ← add_sum_erase _ f' hh,
    ← add_sum_erase _ f (mem_univ i), ← add_sum_erase _ f hh]
  have : ∑ l ∈ ((univ.erase i).erase h), f' l = ∑ l ∈ ((univ.erase i).erase h), f l := by
    apply sum_congr rfl
    intro l hl
    simp only [mem_erase] at hl
    exact heq l hl.2.1 hl.1
  rw [this]
  ring

theorem main {k m : ℕ} (S : Fin k → Finset (Fin m)) (hS : ∀ j, (S j).card ≤ 2) {r : ℕ}
    (X : Fin r → Finset (Fin k)) (hX : ∀ i, (X i).biUnion S = univ) :
    ∃ Y : Fin r → Finset (Fin k), (∀ i, (Y i).biUnion S = univ) ∧
      (∀ j, (∑ i, if j ∈ Y i then 1 else 0 : ℕ) = ∑ i, if j ∈ X i then 1 else 0) ∧
      ∀ i h, (Y i).card ≤ (Y h).card + 1 := by
  suffices H : ∀ n, ∀ Y : Fin r → Finset (Fin k), (∑ i, (Y i).card ^ 2) = n →
      (∀ i, (Y i).biUnion S = univ) →
      (∀ j, (∑ i, if j ∈ Y i then 1 else 0 : ℕ) = ∑ i, if j ∈ X i then 1 else 0) →
      ∃ Z : Fin r → Finset (Fin k), (∀ i, (Z i).biUnion S = univ) ∧
        (∀ j, (∑ i, if j ∈ Z i then 1 else 0 : ℕ) = ∑ i, if j ∈ X i then 1 else 0) ∧
        ∀ i h, (Z i).card ≤ (Z h).card + 1 by
    exact H _ X rfl hX (fun j => rfl)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hn hY hcnt
  by_cases hbal : ∀ i h, (Y i).card ≤ (Y h).card + 1
  · exact ⟨Y, hY, hcnt, hbal⟩
  push Not at hbal
  obtain ⟨i, h, hih⟩ := hbal
  have hne : i ≠ h := by
    rintro rfl
    omega
  obtain ⟨A', B', hA', hB', hand, hor, hcA, hcB⟩ := step S hS (Y i) (Y h) (hY i) (hY h) hih
  set Y' : Fin r → Finset (Fin k) := Function.update (Function.update Y i A') h B' with hY'def
  have hY'i : Y' i = A' := by
    rw [hY'def, Function.update_of_ne hne, Function.update_self]
  have hY'h : Y' h = B' := by
    rw [hY'def, Function.update_self]
  have hY'o : ∀ l, l ≠ i → l ≠ h → Y' l = Y l := by
    intro l h1 h2
    rw [hY'def, Function.update_of_ne h2, Function.update_of_ne h1]
  have key : ∀ g : Finset (Fin k) → ℕ,
      (∑ l, g (Y' l)) + (g (Y i) + g (Y h)) = (∑ l, g (Y l)) + (g (Y' i) + g (Y' h)) :=
    fun g => sum_two (fun l => g (Y l)) (fun l => g (Y' l)) i h hne
      (fun l h1 h2 => by simp only [hY'o l h1 h2])
  refine ih (∑ l, (Y' l).card ^ 2) ?_ Y' rfl ?_ ?_
  · rw [← hn]
    have hk := key (fun s => s.card ^ 2)
    simp only [hY'i, hY'h] at hk
    have hlt2 : A'.card ^ 2 + B'.card ^ 2 < (Y i).card ^ 2 + (Y h).card ^ 2 := by
      rw [← hcA, hcB]
      nlinarith
    omega
  · intro l
    by_cases h1 : l = i
    · rw [h1, hY'i]
      exact hA'
    · by_cases h2 : l = h
      · rw [h2, hY'h]
        exact hB'
      · rw [hY'o l h1 h2]
        exact hY l
  · intro j
    rw [← hcnt j]
    have hk := key (fun s => if j ∈ s then 1 else 0)
    simp only [hY'i, hY'h] at hk
    have h4 : (if j ∈ A' then 1 else 0) + (if j ∈ B' then 1 else 0) =
        ((if j ∈ Y i then 1 else 0) + (if j ∈ Y h then 1 else 0) : ℕ) := by
      have h1 := hand j
      have h2 := hor j
      by_cases a : j ∈ A' <;> by_cases b : j ∈ B' <;> by_cases c : j ∈ Y i <;>
        by_cases d : j ∈ Y h <;> simp_all
    omega

end PEqualNP.Outside.L_lib_1491.P1b

namespace PEqualNP.Outside.L_lib_1491

theorem part1 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
(∀ (k m r : Nat) (S : Fin k → Finset (Fin m)) (X : Fin r → Finset (Fin k)),
  (∀ j, (S j).card ≤ 2) → (∀ i, (X i).biUnion S=Finset.univ) →
  ∃ Y : Fin r → Finset (Fin k), (∀ i, (Y i).biUnion S=Finset.univ) ∧
    (∀ j, ((Finset.univ : Finset (Fin r)).filter (fun i => j ∈ Y i)).card =
          ((Finset.univ : Finset (Fin r)).filter (fun i => j ∈ X i)).card) ∧
    ∀ i h, (Y i).card ≤ (Y h).card+1)) := by
  intro k m r S X hS hX
  have hX' : ∀ i, (X i).biUnion S = Finset.univ := by
    intro i
    convert hX i
  obtain ⟨Y, hY, hcnt, hbal⟩ := P1b.main S hS X hX'
  refine ⟨Y, fun i => ?_, fun j => ?_, hbal⟩
  · convert hY i
  · rw [Finset.card_filter, Finset.card_filter]
    convert hcnt j

end PEqualNP.Outside.L_lib_1491

namespace PEqualNP.Outside.L_lib_1491.P2a

def al (n : Nat) (c : Fin (3*n)) : Fin (3*n+1) := ⟨c.val / 3, by have := c.isLt; omega⟩

def be (n : Nat) (c : Fin (3*n)) : Fin (3*n+1) :=
  ⟨n + 2*(c.val/3) + c.val % 3, by have := c.isLt; omega⟩

def S (n : Nat) (j : Fin (3*n+1)) : Finset (Fin (3*n)) :=
  Finset.univ.filter (fun c => al n c = j ∨ be n c = j)

theorem mem_S {n : Nat} {j : Fin (3*n+1)} {c : Fin (3*n)} :
    c ∈ S n j ↔ (al n c = j ∨ be n c = j) := by
  simp [S]

theorem al_ne_be {n : Nat} (c : Fin (3*n)) : al n c ≠ be n c := by
  intro h
  have h' : c.val / 3 = n + 2*(c.val/3) + c.val % 3 := congrArg Fin.val h
  have := c.isLt
  omega

theorem card_S_le (n : Nat) (j : Fin (3*n+1)) : (S n j).card ≤ 3 := by
  have h := Finset.card_le_card_of_injOn (s := S n j) (t := Finset.range 3)
    (fun c => c.val % 3)
    (by
      intro c _
      simp only [Finset.coe_range, Set.mem_Iio]
      omega)
    (by
      intro c1 h1 c2 h2 h
      simp only [Finset.mem_coe, mem_S] at h1 h2
      have h' : c1.val % 3 = c2.val % 3 := h
      apply Fin.ext
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · have e1 : c1.val / 3 = j.val := congrArg Fin.val h1
        have e2 : c2.val / 3 = j.val := congrArg Fin.val h2
        omega
      · have e1 : c1.val / 3 = j.val := congrArg Fin.val h1
        have e2 : n + 2*(c2.val/3) + c2.val % 3 = j.val := congrArg Fin.val h2
        have := c1.isLt
        omega
      · have e1 : n + 2*(c1.val/3) + c1.val % 3 = j.val := congrArg Fin.val h1
        have e2 : c2.val / 3 = j.val := congrArg Fin.val h2
        have := c2.isLt
        omega
      · have e1 : n + 2*(c1.val/3) + c1.val % 3 = j.val := congrArg Fin.val h1
        have e2 : n + 2*(c2.val/3) + c2.val % 3 = j.val := congrArg Fin.val h2
        omega)
  simpa using h

theorem card_filter_two {n : Nat} (c : Fin (3*n))
    (inst : DecidablePred (fun j : Fin (3*n+1) => c ∈ S n j)) :
    (@Finset.filter _ (fun j : Fin (3*n+1) => c ∈ S n j) inst Finset.univ).card = 2 := by
  classical
  have hs : @Finset.filter _ (fun j : Fin (3*n+1) => c ∈ S n j) inst Finset.univ
      = {al n c, be n c} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_S, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [hs]
  exact Finset.card_pair (al_ne_be c)

end PEqualNP.Outside.L_lib_1491.P2a

namespace PEqualNP.Outside.L_lib_1491

theorem part2 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ n : Nat, 0<n →
  ∃ (S : Fin (3*n+1) → Finset (Fin (3*n))) (A B : Finset (Fin (3*n+1))),
    (∀ j, (S j).card ≤ 3) ∧
    (∀ c, (Finset.univ.filter (fun j : Fin (3*n+1) => c ∈ S j)).card=2) ∧
    A.card=n ∧ B.card=2*n+1 ∧ Disjoint A B ∧ A ∪ B=Finset.univ ∧
    A.biUnion S=Finset.univ ∧ B.biUnion S=Finset.univ ∧
    ∀ U V : Finset (Fin (3*n+1)), Disjoint U V → U ∪ V=Finset.univ →
      U.biUnion S=Finset.univ → V.biUnion S=Finset.univ →
      (U=A ∧ V=B) ∨ (U=B ∧ V=A)) := by
  intro n hn
  refine ⟨P2a.S n, Finset.univ.filter (fun j : Fin (3*n+1) => (j : ℕ) < n),
    Finset.univ.filter (fun j : Fin (3*n+1) => ¬ (j : ℕ) < n),
    fun j => P2a.card_S_le n j, fun c => P2a.card_filter_two c _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.card_filter_val_lt]
    omega
  · have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (3*n+1) => (j : ℕ) < n)
    rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
    omega
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 h1
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  · apply Finset.eq_univ_of_forall
    intro c
    simp only [Finset.mem_biUnion]
    refine ⟨P2a.al n c, ?_, P2a.mem_S.mpr (Or.inl rfl)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show c.val / 3 < n
    have := c.isLt
    omega
  · apply Finset.eq_univ_of_forall
    intro c
    simp only [Finset.mem_biUnion]
    refine ⟨P2a.be n c, ?_, P2a.mem_S.mpr (Or.inr rfl)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show ¬ (n + 2*(c.val/3) + c.val % 3 < n)
    omega
  · intro U V hd hu hU hV

    have notV : ∀ x, x ∈ V ↔ x ∉ U := by
      intro x
      constructor
      · intro hx hxU
        exact Finset.disjoint_left.mp hd hxU hx
      · intro hx
        have hx' : x ∈ (Finset.univ : Finset (Fin (3*n+1))) := Finset.mem_univ x
        rw [← hu] at hx'
        simp only [Finset.mem_union] at hx'
        rcases hx' with h | h
        · exact absurd h hx
        · exact h

    have cov : ∀ c, (P2a.al n c ∈ U ∨ P2a.be n c ∈ U) ∧ (P2a.al n c ∈ V ∨ P2a.be n c ∈ V) := by
      intro c
      have h1 : c ∈ (Finset.univ : Finset (Fin (3*n))) := Finset.mem_univ c
      have h2 : c ∈ (Finset.univ : Finset (Fin (3*n))) := Finset.mem_univ c
      rw [← hU] at h1
      rw [← hV] at h2
      simp only [Finset.mem_biUnion] at h1 h2
      obtain ⟨j, hj, hc⟩ := h1
      obtain ⟨k, hk, hc'⟩ := h2
      rw [P2a.mem_S] at hc hc'
      constructor
      · rcases hc with rfl | rfl
        · exact Or.inl hj
        · exact Or.inr hj
      · rcases hc' with rfl | rfl
        · exact Or.inl hk
        · exact Or.inr hk
    have key : ∀ c, P2a.al n c ∈ U ↔ P2a.be n c ∉ U := by
      intro c
      have h1 := (cov c).1
      have h2 := (cov c).2
      rw [notV, notV] at h2
      tauto

    have chain : ∀ i (hi : i < n),
        ((⟨i, by omega⟩ : Fin (3*n+1)) ∈ U ↔ (⟨0, by omega⟩ : Fin (3*n+1)) ∈ U) := by
      intro i
      induction i with
      | zero => intro _; exact Iff.rfl
      | succ i ih =>
        intro hi
        have k1 := key ⟨3*i+2, by omega⟩
        have k2 := key ⟨3*i+3, by omega⟩
        have e1 : P2a.al n ⟨3*i+2, by omega⟩ = ⟨i, by omega⟩ :=
          Fin.ext (by show (3*i+2)/3 = i; omega)
        have e2 : P2a.al n ⟨3*i+3, by omega⟩ = ⟨i+1, by omega⟩ :=
          Fin.ext (by show (3*i+3)/3 = i+1; omega)
        have e3 : P2a.be n ⟨3*i+2, by omega⟩ = P2a.be n ⟨3*i+3, by omega⟩ :=
          Fin.ext (by
            show n + 2*((3*i+2)/3) + (3*i+2)%3 = n + 2*((3*i+3)/3) + (3*i+3)%3
            omega)
        rw [e1, e3] at k1
        rw [e2] at k2
        exact (k2.trans k1.symm).trans (ih (by omega))

    have surj : ∀ j : Fin (3*n+1), ¬ (j : ℕ) < n → ∃ c, P2a.be n c = j := by
      intro j hj
      have hjl := j.isLt
      by_cases h : j.val - n < 2*n
      · refine ⟨⟨3*((j.val-n)/2) + (j.val-n)%2, by omega⟩, Fin.ext ?_⟩
        show n + 2*((3*((j.val-n)/2) + (j.val-n)%2)/3) + (3*((j.val-n)/2) + (j.val-n)%2)%3
          = j.val
        omega
      · refine ⟨⟨3*n-1, by omega⟩, Fin.ext ?_⟩
        show n + 2*((3*n-1)/3) + (3*n-1)%3 = j.val
        omega
    have hA : ∀ j : Fin (3*n+1), (j : ℕ) < n →
        (j ∈ U ↔ (⟨0, by omega⟩ : Fin (3*n+1)) ∈ U) := by
      intro j hj
      exact chain j.val hj
    have hB : ∀ j : Fin (3*n+1), ¬ (j : ℕ) < n →
        (j ∈ U ↔ (⟨0, by omega⟩ : Fin (3*n+1)) ∉ U) := by
      intro j hj
      obtain ⟨c, rfl⟩ := surj j hj
      have ha := hA (P2a.al n c) (by show c.val / 3 < n; have := c.isLt; omega)
      have hk := key c
      tauto
    by_cases h0 : (⟨0, by omega⟩ : Fin (3*n+1)) ∈ U
    · left
      constructor
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : (j : ℕ) < n
        · have := hA j hj
          tauto
        · have := hB j hj
          tauto
      · ext j
        rw [notV]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : (j : ℕ) < n
        · have := hA j hj
          tauto
        · have := hB j hj
          tauto
    · right
      constructor
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : (j : ℕ) < n
        · have := hA j hj
          tauto
        · have := hB j hj
          tauto
      · ext j
        rw [notV]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : (j : ℕ) < n
        · have := hA j hj
          tauto
        · have := hB j hj
          tauto

end PEqualNP.Outside.L_lib_1491

theorem PEqualNP.Outside.L_lib_1491 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
(∀ (k m r : Nat) (S : Fin k → Finset (Fin m)) (X : Fin r → Finset (Fin k)),
  (∀ j, (S j).card ≤ 2) → (∀ i, (X i).biUnion S=Finset.univ) →
  ∃ Y : Fin r → Finset (Fin k), (∀ i, (Y i).biUnion S=Finset.univ) ∧
    (∀ j, ((Finset.univ : Finset (Fin r)).filter (fun i => j ∈ Y i)).card =
          ((Finset.univ : Finset (Fin r)).filter (fun i => j ∈ X i)).card) ∧
    ∀ i h, (Y i).card ≤ (Y h).card+1) ∧
∀ n : Nat, 0<n →
  ∃ (S : Fin (3*n+1) → Finset (Fin (3*n))) (A B : Finset (Fin (3*n+1))),
    (∀ j, (S j).card ≤ 3) ∧
    (∀ c, (Finset.univ.filter (fun j : Fin (3*n+1) => c ∈ S j)).card=2) ∧
    A.card=n ∧ B.card=2*n+1 ∧ Disjoint A B ∧ A ∪ B=Finset.univ ∧
    A.biUnion S=Finset.univ ∧ B.biUnion S=Finset.univ ∧
    ∀ U V : Finset (Fin (3*n+1)), Disjoint U V → U ∪ V=Finset.univ →
      U.biUnion S=Finset.univ → V.biUnion S=Finset.univ →
      (U=A ∧ V=B) ∨ (U=B ∧ V=A)) := by
  exact ⟨PEqualNP.Outside.L_lib_1491.part1, PEqualNP.Outside.L_lib_1491.part2⟩
