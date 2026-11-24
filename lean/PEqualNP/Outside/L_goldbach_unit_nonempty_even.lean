import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  dsimp only
  intro q n hq hn
  classical
  let r (p : ℕ) : ℕ := if n % p = 1 then 2 else 1
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset r id q.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp t ht hpt =>
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors ht)).2 hpt)
  let a := x % q
  have ha : a < q := Nat.mod_lt _ hq
  have hlocal (p : ℕ) (hp : p.Prime) (hd : p ∣ q) :
      a % p ≠ 0 ∧ a % p ≠ n % p := by
    have hres : a % p = r p % p :=
      (Nat.ModEq.of_dvd hd (Nat.mod_modEq x q)).trans (hx p (hp.mem_primeFactors hd hq.ne'))
    have hp1 := hp.one_lt
    rw [hres]
    by_cases h : n % p = 1
    · have hp2 : 2 < p := by
        by_contra! hle
        have heq : p = 2 := by omega
        obtain ⟨j, hj⟩ := hn
        subst p
        omega
      simp [r, h, Nat.mod_eq_of_lt hp2]
    · simp [r, h, Nat.mod_eq_of_lt hp1, Ne.symm h]
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, ?_, ?_⟩⟩
  · by_contra h
    obtain ⟨p, hp, hpa, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact (hlocal p hp hpq).1 (Nat.mod_eq_zero_of_dvd hpa)
  · by_contra h
    obtain ⟨p, hp, hpb, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hadd : (n + q - a) + a = n + q := by omega
    have hcong : (n + q) % p = a % p := by
      calc
        (n + q) % p = ((n + q - a) + a) % p := congrArg (fun t => t % p) hadd.symm
        _ = a % p := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpb, zero_add, Nat.mod_mod]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpq, add_zero, Nat.mod_mod] at hcong
    exact (hlocal p hp hpq).2 hcong.symm
