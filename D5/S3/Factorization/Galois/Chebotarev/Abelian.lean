/- GID: D5/S3/Factorization/Galois/Chebotarev/Abelian
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/Abelian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abelian Chebotarev fibres have inverse Galois-group Dirichlet density. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.AbelianCrossing

/-!
# Chebotarev's theorem: abelian case

The finite-group order estimates, density-ratio argument, and final abelian
Chebotarev theorem use the cyclotomic-crossing density bound.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open NumberField Filter Topology Set

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! #### Number-theoretic helpers for the exponent-keyed density bound

The argument controls elements whose order misses a prescribed prime power using
the exponent of a finite commutative group. -/

/-- Per-`σ` lower bound `δ_inf(S_σ) ≥ 1/|G|`, the limit of the per-`m` bound
`liminf_density_S_sigma_ge_card_H_n_div_GH` as `m → ∞` along a sequence of
*admissible primes* `m_k ≡ 1 (mod 4·n^k)` with `m_k > |disc L|` (Dirichlet's theorem on
primes in arithmetic progression). The lower half of Sharifi 7.2.2 Step 2 (p. 144). -/
theorem liminf_ratio_ge_inv_card_G
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    (Nat.card Gal(L/K) : ℝ)⁻¹
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set n : ℕ := Nat.card Gal(L/K) with hn
  set L_inf : ℝ :=
    Filter.liminf
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) with hLinf
  have hnpos : 0 < n := hn ▸ Nat.card_pos
  have hn1 : 1 ≤ n := hnpos
  set dB : ℕ := (NumberField.discr L).natAbs with hdB
  have hdBpos : 0 < dB := by
    rw [hdB, Int.natAbs_pos]
    exact NumberField.discr_ne_zero L
  have hprime : ∀ k : ℕ,
      ∃ m : ℕ, m.Prime ∧ dB < m ∧ m % 4 ≠ 2 ∧ n ^ k ∣ m - 1 := by
    intro k
    obtain ⟨m, hmgt, hmp, hmeq⟩ := Nat.forall_exists_prime_gt_and_modEq (max dB 1)
      (q := 4 * n ^ k) (by positivity) (Nat.coprime_one_left _)
    have hdvd : 4 * n ^ k ∣ m - 1 := (Nat.modEq_iff_dvd' hmp.one_lt.le).mp hmeq.symm
    refine ⟨m, hmp, by omega, ?_, dvd_trans ⟨4, by ring⟩ hdvd⟩
    have := dvd_trans ⟨n ^ k, rfl⟩ hdvd
    omega
  choose m hmp hmgt hm4 hmdvd using hprime
  have hm1 : ∀ k, 1 ≤ m k := fun k ↦ (hmp k).one_lt.le
  have hmne : ∀ k, m k ≠ 0 := fun k ↦ (hmp k).pos.ne'
  have hmNeZero : ∀ k, NeZero (m k) := fun k ↦ ⟨hmne k⟩
  have hmcop : ∀ k, dB.Coprime (m k) := fun k ↦ by
    rw [Nat.coprime_comm, (hmp k).coprime_iff_not_dvd]
    exact fun hdvd ↦ absurd (Nat.le_of_dvd hdBpos hdvd) (Nat.not_le.mpr (hmgt k))
  have hexp : ∀ k, Monoid.exponent (ZMod (m k))ˣ = m k - 1 := fun k ↦ by
    haveI : Fact (m k).Prime := ⟨hmp k⟩
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (hmp k)]
  have hbound : ∀ k : ℕ,
      (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹ ≤ L_inf := by
    intro k
    have hbnd := liminf_density_S_sigma_ge_card_H_n_div_GH K L σ (m k) (hm1 k) (hm4 k)
      (hdB ▸ hmcop k)
    rw [← hn, ← hLinf] at hbnd
    refine le_trans (le_of_eq ?_) hbnd
    have hHpos : (0 : ℝ) < Nat.card ((ZMod (m k))ˣ) := by
      have := hmNeZero k
      exact_mod_cast Nat.card_pos
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    field_simp
  have hexpdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors,
      p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ := fun k _ p hp ↦ by
    rw [hexp k]
    refine dvd_trans ?_ (hmdvd k)
    calc p ^ (k * n.factorization p) = (p ^ n.factorization p) ^ k := by rw [← pow_mul, mul_comm]
      _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
  have htends : Filter.Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹)
      Filter.atTop (𝓝 ((n : ℝ)⁻¹)) := by
    simpa using
      ((show ∀ (n : ℕ) (hn1 : 1 ≤ n) (m : ℕ → ℕ) (hmNeZero : ∀ k, NeZero (m k)) (hdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors, p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ), (Filter.Tendsto (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ) / Nat.card ((ZMod (m k))ˣ)) Filter.atTop (𝓝 1)) from by
        intro n hn1 m hmNeZero hdvd
        classical
        rcases eq_or_lt_of_le hn1 with hn1' | hn2'
        · have hconst : ∀ k, (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
              / Nat.card ((ZMod (m k))ˣ) = 1 := fun k ↦ by
            have := hmNeZero k
            rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x ↦ hn1'.symm ▸ one_dvd _)),
              div_self (by exact_mod_cast Nat.card_pos.ne')]
          rw [tendsto_congr hconst]
          exact tendsto_const_nhds
        · have hn2 : 2 ≤ n := hn2'
          set S : ℕ → ℝ := fun k ↦ ∑ p ∈ n.primeFactors,
            (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
          have hSt : Filter.Tendsto S Filter.atTop (𝓝 0) := by
            rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
            refine tendsto_finsetSum _ (fun p hp ↦ ?_)
            have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
            exact (show ∀ (p v : ℕ) (hp : 2 ≤ p) (hv : 1 ≤ v), (Tendsto (fun k : ℕ ↦ (1 : ℝ) / (p : ℝ) ^ (k * v - v - 1)) atTop (𝓝 0)) from by
              intro p v hp hv
              classical
              have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
              have hpinv1 : (p : ℝ)⁻¹ < 1 := by
                rw [inv_lt_one₀ hp0]; exact_mod_cast hp.trans_lt' Nat.one_lt_two
              have hbase : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
                tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hpinv1
              have hexp : Tendsto (fun k : ℕ ↦ k * v - v - 1) atTop atTop := by
                refine tendsto_atTop_mono (f := fun k : ℕ ↦ k - (v + 1)) (fun k ↦ ?_)
                  (tendsto_sub_atTop_nat (v + 1))
                have : k ≤ k * v := Nat.le_mul_of_pos_right k hv; lia
              refine (hbase.comp hexp).congr (fun k ↦ ?_)
              simp [Function.comp_apply, one_div, inv_pow]) p (n.factorization p) hpp.two_le
              (Nat.Prime.factorization_pos_of_dvd hpp (by lia) (Nat.dvd_of_mem_primeFactors hp))
          have hlo : Filter.Tendsto (fun k ↦ 1 - S k) Filter.atTop (𝓝 1) := by
            simpa using hSt.const_sub 1
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_
            (Filter.Eventually.of_forall (fun k ↦ ?_))
          · filter_upwards [Filter.eventually_ge_atTop 1] with k hk1
            haveI : NeZero (m k) := hmNeZero k
            have hlocalRatio : ∀ (n kBound : ℕ) (hn2 : 2 ≤ n) (hk : 1 ≤ kBound) (hexp : ∀ p ∈ n.primeFactors, p ^ (kBound * n.factorization p) ∣ Monoid.exponent ((ZMod (m k))ˣ)), (1 - (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ^ (kBound * n.factorization p - n.factorization p - 1)) ≤ (Nat.card {τ : ((ZMod (m k))ˣ) // n ∣ orderOf τ} : ℝ) / Nat.card ((ZMod (m k))ˣ)) := by
              intro n kBound hn2 hk hexp
              classical
              classical
              set total : ℕ := Nat.card ((ZMod (m k))ˣ) with htotal
              set good : ℕ := Nat.card {τ : ((ZMod (m k))ˣ) // n ∣ orderOf τ} with hgood
              set bad : ℕ := Nat.card {τ : ((ZMod (m k))ˣ) // ¬ n ∣ orderOf τ} with hbad
              have htotpos : 0 < total := Nat.card_pos
              have hgb : good + bad = total := by
                have : Fintype ((ZMod (m k))ˣ) := Fintype.ofFinite ((ZMod (m k))ˣ)
                rw [hgood, hbad, htotal]
                simp only [Nat.card_eq_fintype_card]
                rw [Fintype.card_subtype_compl]
                have hle : Fintype.card {τ : ((ZMod (m k))ˣ) // n ∣ orderOf τ} ≤ Fintype.card ((ZMod (m k))ˣ) := Fintype.card_subtype_le _
                lia
              have hbadratio : (bad : ℝ) / total
                  ≤ ∑ p ∈ n.primeFactors,
                      (1 : ℝ) / (p : ℝ) ^ (kBound * n.factorization p - n.factorization p - 1) := by
                refine (show ∀ (bad total : ℕ) (s : Finset ℕ) (badp : ℕ → ℕ) (e : ℕ → ℕ) (P : ℕ → ℕ) (htot : 0 < total) (hcover : bad ≤ ∑ p ∈ s, badp p) (hP : ∀ p ∈ s, 0 < P p) (hbound : ∀ p ∈ s, badp p * (P p) ^ (e p) ≤ total), ((bad : ℝ) / total ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p)) from by
                  intro bad total s badp e P htot hcover hP hbound
                  classical
                  have htotR : (0 : ℝ) < total := by exact_mod_cast htot
                  have hnum : (bad : ℝ) ≤ ∑ p ∈ s, (badp p : ℝ) := by
                    calc (bad : ℝ) ≤ ((∑ p ∈ s, badp p : ℕ) : ℝ) := by exact_mod_cast hcover
                      _ = ∑ p ∈ s, (badp p : ℝ) := by push_cast; ring
                  calc (bad : ℝ) / total
                      ≤ (∑ p ∈ s, (badp p : ℝ)) / total := by gcongr
                    _ = ∑ p ∈ s, (badp p : ℝ) / total := by rw [Finset.sum_div]
                    _ ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
                        refine Finset.sum_le_sum (fun p hps ↦ ?_)
                        have hPp : (0 : ℝ) < (P p : ℝ) ^ (e p) := by have := hP p hps; positivity
                        rw [div_le_div_iff₀ htotR hPp, one_mul]
                        calc (badp p : ℝ) * (P p : ℝ) ^ (e p) = ((badp p * (P p) ^ (e p) : ℕ) : ℝ) := by
                              push_cast; ring
                          _ ≤ (total : ℝ) := by exact_mod_cast hbound p hps) bad total n.primeFactors
                  (fun p ↦ Nat.card {τ : ((ZMod (m k))ˣ) // ¬ p ^ n.factorization p ∣ orderOf τ})
                  (fun p ↦ kBound * n.factorization p - n.factorization p - 1) (fun p ↦ p)
                  htotpos ?_ ?_ ?_
                · rw [hbad]
                  refine (show ∀ (s : Finset ℕ) (P : ((ZMod (m k))ˣ) → Prop) (Q : ℕ → ((ZMod (m k))ˣ) → Prop) (h : ∀ x, P x → ∃ i ∈ s, Q i x), (Nat.card {x : ((ZMod (m k))ˣ) // P x} ≤ ∑ i ∈ s, Nat.card {x : ((ZMod (m k))ˣ) // Q i x}) from by
                    intro s P Q h
                    classical
                    classical
                    have : Fintype ((ZMod (m k))ˣ) := Fintype.ofFinite ((ZMod (m k))ˣ)
                    simp only [Nat.card_eq_fintype_card]
                    calc Fintype.card {x : ((ZMod (m k))ˣ) // P x}
                        = (Finset.univ.filter P).card := by rw [Fintype.card_subtype]
                      _ ≤ (s.biUnion (fun i ↦ Finset.univ.filter (Q i))).card := by
                          refine Finset.card_le_card (fun x hx ↦ ?_)
                          rw [Finset.mem_filter] at hx
                          obtain ⟨i, hi, hqi⟩ := h x hx.2
                          exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hqi⟩⟩
                      _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
                      _ = ∑ i ∈ s, Fintype.card {x : ((ZMod (m k))ˣ) // Q i x} :=
                          Finset.sum_congr rfl (fun i _ ↦ by rw [Fintype.card_subtype])) n.primeFactors (fun τ ↦ ¬ n ∣ orderOf τ)
                    (fun p τ ↦ ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ ↦ ?_)
                  exact (show ∀ (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) (hndvd : ¬ n ∣ d), (∃ p ∈ n.primeFactors, ¬ p ^ (n.factorization p) ∣ d) from by
                    intro n d hn hd hndvd
                    classical
                    by_contra! hcon
                    apply hndvd
                    rw [← Nat.factorization_le_iff_dvd hn hd]
                    intro p
                    by_cases hp : p ∈ n.primeFactors
                    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
                      exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hd).mp (hcon p hp)
                    · have hzero : n.factorization p = 0 := by
                        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
                      rw [hzero]; exact Nat.zero_le _) n (orderOf τ) (by lia) (orderOf_pos τ).ne' hτ
                · exact fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
                · intro p hp
                  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
                  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
                  have hv1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hpp (by lia) hpn
                  have hav : n.factorization p ≤ kBound * n.factorization p := Nat.le_mul_of_pos_left _ hk
                  have hlocalPrime : ∀ (p a v : ℕ) (hp : p.Prime) (hv1 : 1 ≤ v) (hav : v ≤ a) (hdvd : p ^ a ∣ Monoid.exponent ((ZMod (m k))ˣ)), (Nat.card {x : ((ZMod (m k))ˣ) // ¬ p ^ v ∣ orderOf x} * p ^ (a - v - 1) ≤ Nat.card ((ZMod (m k))ˣ)) := by
                    intro p a v hp hv1 hav hdvd
                    classical
                    have haE : a ≤ (Monoid.exponent ((ZMod (m k))ˣ)).factorization p :=
                      (Nat.Prime.pow_dvd_iff_le_factorization hp
                        (Monoid.exponent_ne_zero_of_finite (G := (ZMod (m k))ˣ))).mp hdvd
                    exact (show ∀ (p v e : ℕ) (hp : p.Prime) (hv1 : 1 ≤ v) (he : e + (v - 1) ≤ (Monoid.exponent ((ZMod (m k))ˣ)).factorization p), (Nat.card {x : ((ZMod (m k))ˣ) // ¬ p ^ v ∣ orderOf x} * p ^ e ≤ Nat.card ((ZMod (m k))ˣ)) from by
                      intro p v e hp hv1 he
                      classical
                      classical
                      set E := Monoid.exponent ((ZMod (m k))ˣ) with hE
                      have hEne : E ≠ 0 := by
                        rw [hE]
                        exact Monoid.exponent_ne_zero_of_finite (G := (ZMod (m k))ˣ)
                      set M := ordCompl[p] E * p ^ (v - 1)
                      have hMne : M ≠ 0 := mul_ne_zero (Nat.ordCompl_pos p hEne).ne' (pow_ne_zero _ hp.ne_zero)
                      have hle1 : v - 1 ≤ E.factorization p := by lia
                      have hMdvdE : M ∣ E := (show ∀ (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hle : v - 1 ≤ E.factorization p), (ordCompl[p] E * p ^ (v - 1) ∣ E) from by
                        intro E p v hp hE hle
                        classical
                        rw [← Nat.factorization_le_iff_dvd
                          (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)) hE]
                        intro q
                        rw [(show ∀ (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (q : ℕ), ((ordCompl[p] E * p ^ (v - 1)).factorization q = if q = p then v - 1 else E.factorization q) from by
                          intro E p v hp hE q
                          classical
                          rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
                          simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
                            Nat.factorization_ordCompl]
                          by_cases hq : q = p
                          · subst hq; rw [Finsupp.erase_same, if_pos rfl, if_pos rfl, zero_add]
                          · rw [Finsupp.erase_ne hq, if_neg fun h ↦ hq h.symm, if_neg hq, add_zero]) E p v hp hE q]
                        by_cases hq : q = p
                        · subst hq; rwa [if_pos rfl]
                        · rw [if_neg hq]) E p v hp hEne hle1
                      have hgcd : Nat.gcd E M = M := Nat.gcd_eq_right hMdvdE
                      have hEdivM : E / M = p ^ (E.factorization p - (v - 1)) :=
                        Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hMne) (by
                          rw [mul_assoc, ← pow_add,
                            show v - 1 + (E.factorization p - (v - 1)) = E.factorization p by lia,
                            mul_comm (ordCompl[p] E), Nat.ordProj_mul_ordCompl_eq_self])
                      have hbad_sub : Nat.card {x : ((ZMod (m k))ˣ) // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} := by
                        refine Nat.card_le_card_of_injective _
                          (Subtype.impEmbedding _ _ (fun x hx ↦ ?_)).injective
                        rw [← orderOf_dvd_iff_pow_eq_one]
                        refine (show ∀ (E d p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hd : d ∣ E) (hvp : d.factorization p ≤ v - 1), (d ∣ ordCompl[p] E * p ^ (v - 1)) from by
                          intro E d p v hp hE hd hvp
                          classical
                          have hdne : d ≠ 0 := fun h ↦ by subst h; exact hE (Nat.eq_zero_of_zero_dvd hd)
                          rw [← Nat.factorization_le_iff_dvd hdne
                            (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero))]
                          intro q
                          rw [(show ∀ (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (q : ℕ), ((ordCompl[p] E * p ^ (v - 1)).factorization q = if q = p then v - 1 else E.factorization q) from by
                            intro E p v hp hE q
                            classical
                            rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
                            simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
                              Nat.factorization_ordCompl]
                            by_cases hq : q = p
                            · subst hq; rw [Finsupp.erase_same, if_pos rfl, if_pos rfl, zero_add]
                            · rw [Finsupp.erase_ne hq, if_neg fun h ↦ hq h.symm, if_neg hq, add_zero]) E p v hp hE q]
                          by_cases hq : q = p
                          · subst hq; rwa [if_pos rfl]
                          · rw [if_neg hq]; exact (Nat.factorization_le_iff_dvd hdne hE).mpr hd q) E (orderOf x) p v hp hEne ?_ ?_
                        · rw [hE]; exact Monoid.order_dvd_exponent x
                        · by_contra! hcon
                          exact hx ((Nat.Prime.pow_dvd_iff_le_factorization hp (orderOf_pos x).ne').mpr (by lia))
                      have hEM : p ^ e ≤ E / M := by
                        rw [hEdivM]; exact pow_le_pow_right₀ hp.one_le (by lia)
                      calc Nat.card {x : ((ZMod (m k))ˣ) // ¬ p ^ v ∣ orderOf x} * p ^ e
                          ≤ Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} * p ^ e := Nat.mul_le_mul_right _ hbad_sub
                        _ ≤ Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} * (E / M) := Nat.mul_le_mul_left _ hEM
                        _ = Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} * (E / Nat.gcd E M) := by rw [hgcd]
                        _ ≤ Nat.card ((ZMod (m k))ˣ) := (show ∀ (M : ℕ), (Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} * (Monoid.exponent ((ZMod (m k))ˣ) / Nat.gcd (Monoid.exponent ((ZMod (m k))ˣ)) M) ≤ Nat.card ((ZMod (m k))ˣ)) from by
                          intro M
                          classical
                          classical
                          set f : ((ZMod (m k))ˣ) →* ((ZMod (m k))ˣ) := powMonoidHom M with hf
                          have hker : Nat.card f.ker = Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} :=
                            Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by rw [MonoidHom.mem_ker]; rfl)
                          have hcard : Nat.card f.ker * Nat.card f.range = Nat.card ((ZMod (m k))ˣ) := by
                            rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
                              Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
                            ring
                          obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent
                            (Monoid.ExponentExists.of_finite (G := (ZMod (m k))ˣ))
                          have hord : orderOf (g ^ M) = Monoid.exponent ((ZMod (m k))ˣ) / Nat.gcd (Monoid.exponent ((ZMod (m k))ˣ)) M := by
                            rw [orderOf_pow, hg]
                          have hle : orderOf (g ^ M) ≤ Nat.card f.range := by
                            rw [← Nat.card_zpowers]
                            exact Nat.card_le_card_of_injective (Subgroup.inclusion (by
                              rw [Subgroup.zpowers_le]; exact ⟨g, rfl⟩)) (Subgroup.inclusion_injective _)
                          rw [← hord]
                          calc Nat.card {x : ((ZMod (m k))ˣ) // x ^ M = 1} * orderOf (g ^ M)
                              = Nat.card f.ker * orderOf (g ^ M) := by rw [hker]
                            _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul_left _ hle
                            _ = Nat.card ((ZMod (m k))ˣ) := hcard) M) p v _ hp hv1 (by lia)
                  exact hlocalPrime p (kBound * n.factorization p) (n.factorization p)
                    hpp hv1 hav (hexp p hp)
              have htk : (total : ℝ) ≠ 0 := by exact_mod_cast htotpos.ne'
              have heq : (good : ℝ) / total = 1 - (bad : ℝ) / total := by
                have hgbk : (good : ℝ) + (bad : ℝ) = (total : ℝ) := by exact_mod_cast hgb
                field_simp
                linarith [hgbk]
              rw [heq]
              linarith [hbadratio]
            simpa only [hSdef] using hlocalRatio n k hn2 hk1 (hdvd k hk1)
          · have := hmNeZero k
            rw [div_le_one (by exact_mod_cast (Nat.card_pos : 0 < Nat.card ((ZMod (m k))ˣ)))]
            exact_mod_cast Nat.card_le_card_of_injective
              (Subtype.val : {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} → _) Subtype.val_injective) n hn1 m hmNeZero hexpdvd).mul_const ((n : ℝ)⁻¹)
  exact le_of_tendsto htends (Filter.Eventually.of_forall hbound)

/-- The density ratios of the `|G|` Frobenius-fibres `S_σ` (over
`σ ∈ Gal(L/K)`) sum to the ratio for the unramified primes, which tends
to `1` as `s ↓ 1` since the ramified primes are finite.
Sharifi 7.2.2 Step 2: the `S_σ`
partition the unramified primes. -/
theorem ratioSum_frobeniusFibres_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] :
    Filter.Tendsto
      (fun s : ℝ ↦ ∑ σ : Gal(L/K),
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  classical
  set S : Gal(L/K) → Set (Ideal (𝓞 K)) := fun σ ↦
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hS
  set R : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
  set D : ℝ → ℝ := primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) with hD
  letI : CommMonoid Gal(L/K) := IsMulCommutative.instCommMonoid
  have hmk_inj : Function.Injective (ConjClasses.mk : Gal(L/K) → ConjClasses Gal(L/K)) :=
    ConjClasses.mk_injective
  have hpd : ((Finset.univ : Finset Gal(L/K)) : Set Gal(L/K)).PairwiseDisjoint S := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun 𝔭 ha hb ↦ hab (hmk_inj ?_)
    rw [hS] at ha hb
    exact ha.2.2.symm.trans hb.2.2
  have hdisjR : Disjoint (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) R := by
    refine Set.disjoint_left.mpr fun 𝔭 hmem hbad ↦ ?_
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    exact hbad.2.2 (hS ▸ hσ).2.1
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔭 ∈ (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) ∪ R := by
    intro 𝔭 hp hne
    by_cases hunr : UnramifiedIn K L 𝔭
    · obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (frobeniusClass K L 𝔭)
      exact Or.inl <| Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨Finset.mem_univ σ,
        hS ▸ ⟨hp, hunr, hσ.symm⟩⟩⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := by
    let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
      FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
    have : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
      FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
    have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
      rw [Ideal.zero_eq_bot]
      exact differentIdeal_ne_bot
    apply Set.Finite.subset
      ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 K)))
    rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
    simp only [UnramifiedIn, not_and, not_forall] at hnunr
    obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
    have := h𝔓max.isPrime
    have := h𝔓lo
    have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
    have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      by_contra h
      exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
    exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩
  have hR0 : Filter.Tendsto (fun s ↦ primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 0) :=
    hasDirichletDensity_of_finite K hRfin
  have hDpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < D s :=
    (primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0
  have hcomp : Filter.Tendsto (fun s ↦ 1 - primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 1) := by
    simpa using hR0.const_sub 1
  refine hcomp.congr' ?_
  filter_upwards [hDpos, self_mem_nhdsWithin] with s hpos hs1
  simp only [Set.mem_Ioi] at hs1
  have hsum : ∑ σ : Gal(L/K), primeIdealZetaSum (S σ) s
      = primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s :=
    ((show ∀ (t : Finset Gal(L/K)) (g : Gal(L/K) → Set (Ideal (𝓞 K))), (t : Set Gal(L/K)).PairwiseDisjoint g → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s from by
      intro t g hg s hs
      classical
      induction t using Finset.induction with
      | empty =>
          have hzero : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
            have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
                𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨(·.2.1)⟩
            rw [primeIdealZetaSum, tsum_empty]
          simp [hzero]
      | insert a t ha ih =>
          have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
            disjoint_iUnion₂_right.2 fun i hi ↦
              hg (t.mem_insert_self a) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
          rw [Finset.set_biUnion_insert, (show ∀ {S T : Set (Ideal (𝓞 K))}, Disjoint S T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s from by
            intro S T hDisj s hs
            let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
                ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
              { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
                invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
            let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
                ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
              { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
                  fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
                invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
                left_inv := fun _ ↦ rfl
                right_inv := fun _ ↦ rfl }
            rw [primeIdealZetaSum, primeIdealZetaSum, primeIdealZetaSum,
              ← ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
                intro S s hs
                exact (((show Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
                  (((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
                    have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
                    classical
                    haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
                      Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
                        ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                        (fun _ _ _ _ ↦ Subtype.ext)
                    have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                      classical
                      have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ))
                          =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                        classical
                        have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                          Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                            (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) b)
                        have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity K k =
                            Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                          have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal K ↦
                            Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                          rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                              {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ n} by
                            ext ⟨I, hI⟩
                            simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                            exact ⟨fun h ↦ h.2, fun h ↦
                              ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                          exact key.symm
                        have h_card_bridge : ∀ n : ℕ,
                            Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} =
                            Nat.card {I : (Ideal (𝓞 K))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                          fun n ↦ Nat.card_congr
                            { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                                ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                              invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                                ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                              left_inv := fun _ ↦ rfl
                              right_inv := fun _ ↦ rfl }
                        refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                          (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
                            tendsto_natCast_atTop_atTop).congr' ?_)
                        filter_upwards with n
                        simp only [Function.comp_apply, Real.rpow_one]
                        rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                        push_cast
                        rfl
                      have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s :=
                        LSeriesSummable_of_sum_norm_bigO_and_nonneg
                          (f := fun n ↦ (idealNormMultiplicity K n : ℝ))
                          hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                          (by exact_mod_cast hcondition)
                      have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) (s : ℂ) =
                          fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                        funext n
                        simp only [LSeries.term]
                        split_ifs with hn
                        · subst hn
                          have hzero : idealNormMultiplicity K 0 = 0 := by
                              unfold idealNormMultiplicity
                              rw [Nat.card_eq_zero]
                              exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                          simp [hzero]
                        · simp [Complex.cpow_neg, div_eq_mul_inv]
                      exact (h_term_eq ▸ h_lss :
                        Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
                    have hzeta : NumberField.dedekindZeta K (s : ℂ) =
                        ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                      unfold NumberField.dedekindZeta LSeries
                      refine tsum_congr fun n ↦ ?_
                      unfold LSeries.term
                      rcases Nat.eq_zero_or_pos n with rfl | hn
                      · have hs0 : (s : ℂ) ≠ 0 := by
                          intro hzero
                          have hre := congrArg Complex.re hzero
                          simp only [Complex.zero_re] at hre
                          rw [hre] at hcondition
                          norm_num at hcondition
                        have hzero : idealNormMultiplicity K 0 = 0 := by
                            unfold idealNormMultiplicity
                            rw [Nat.card_eq_zero]
                            exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                        simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                      · simp only [hn.ne', ↓reduceIte]
                        rw [Complex.cpow_neg, div_eq_mul_inv]
                        congr 1
                        unfold idealNormMultiplicity
                        have hequiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≃
                            {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := by
                          refine {
                            toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                            invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                            left_inv := fun _ ↦ rfl
                            right_inv := fun _ ↦ rfl }
                          intro h
                          rw [h, Ideal.absNorm_bot] at hI
                          lia
                        exact_mod_cast Nat.card_congr hequiv
                    set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1)
                    have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                        (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                      fun n ↦ by
                        rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                            (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity K n • (n : ℂ) ^ (-(s : ℂ)) from
                          (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                            (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
                    have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                        ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                      fun n ↦ by
                        rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                            ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                          (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                            (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                          Complex.norm_natCast]
                    have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                      rw [← e.summable_iff]
                      refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                      exact hseries.congr fun n ↦ (hnorm n).symm
                    have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
                        (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                      (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                        hsummable.of_norm
                    have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                        = NumberField.dedekindZeta K s := by
                      rw [hzeta,
                        ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                      exact tsum_congr hval
                    exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
                    fun I ↦ (Complex.norm_natCast_cpow_of_pos
                      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
                  (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                    (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
                  fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
                {x | (x.1 : Ideal (𝓞 K)) ∈ S},
              ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
              ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
            rfl) hdisj hs,
            Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]) Finset.univ S hpd hs1).symm
  have hadd : primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s
      + primeIdealZetaSum R s = D s := by
    rw [← (show ∀ {S T : Set (Ideal (𝓞 K))}, Disjoint S T → ∀ {s : ℝ}, 1 < s → primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s from by
      intro S T hDisj s hs
      let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
          ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
        { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
          invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
          ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
        { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
            fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
          invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [primeIdealZetaSum, primeIdealZetaSum, primeIdealZetaSum,
        ← ((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
          intro S s hs
          exact (((show Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
            (((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
              have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
              classical
              haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
                Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
                  ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                  (fun _ _ _ _ ↦ Subtype.ext)
              have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                classical
                have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ))
                    =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                  classical
                  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                    Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) b)
                  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity K k =
                      Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal K ↦
                      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                    rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                        {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ n} by
                      ext ⟨I, hI⟩
                      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                      exact ⟨fun h ↦ h.2, fun h ↦
                        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                    exact key.symm
                  have h_card_bridge : ∀ n : ℕ,
                      Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} =
                      Nat.card {I : (Ideal (𝓞 K))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                    fun n ↦ Nat.card_congr
                      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                        left_inv := fun _ ↦ rfl
                        right_inv := fun _ ↦ rfl }
                  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
                      tendsto_natCast_atTop_atTop).congr' ?_)
                  filter_upwards with n
                  simp only [Function.comp_apply, Real.rpow_one]
                  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                  push_cast
                  rfl
                have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s :=
                  LSeriesSummable_of_sum_norm_bigO_and_nonneg
                    (f := fun n ↦ (idealNormMultiplicity K n : ℝ))
                    hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                    (by exact_mod_cast hcondition)
                have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) (s : ℂ) =
                    fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                  funext n
                  simp only [LSeries.term]
                  split_ifs with hn
                  · subst hn
                    have hzero : idealNormMultiplicity K 0 = 0 := by
                        unfold idealNormMultiplicity
                        rw [Nat.card_eq_zero]
                        exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                    simp [hzero]
                  · simp [Complex.cpow_neg, div_eq_mul_inv]
                exact (h_term_eq ▸ h_lss :
                  Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
              have hzeta : NumberField.dedekindZeta K (s : ℂ) =
                  ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                unfold NumberField.dedekindZeta LSeries
                refine tsum_congr fun n ↦ ?_
                unfold LSeries.term
                rcases Nat.eq_zero_or_pos n with rfl | hn
                · have hs0 : (s : ℂ) ≠ 0 := by
                    intro hzero
                    have hre := congrArg Complex.re hzero
                    simp only [Complex.zero_re] at hre
                    rw [hre] at hcondition
                    norm_num at hcondition
                  have hzero : idealNormMultiplicity K 0 = 0 := by
                      unfold idealNormMultiplicity
                      rw [Nat.card_eq_zero]
                      exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                  simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                · simp only [hn.ne', ↓reduceIte]
                  rw [Complex.cpow_neg, div_eq_mul_inv]
                  congr 1
                  unfold idealNormMultiplicity
                  have hequiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≃
                      {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := by
                    refine {
                      toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                      invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                      left_inv := fun _ ↦ rfl
                      right_inv := fun _ ↦ rfl }
                    intro h
                    rw [h, Ideal.absNorm_bot] at hI
                    lia
                  exact_mod_cast Nat.card_congr hequiv
              set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1)
              have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                  (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                fun n ↦ by
                  rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                      (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity K n • (n : ℂ) ^ (-(s : ℂ)) from
                    (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                      (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
              have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                  ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                fun n ↦ by
                  rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                      ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                    (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                      (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                    Complex.norm_natCast]
              have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                rw [← e.summable_iff]
                refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                exact hseries.congr fun n ↦ (hnorm n).symm
              have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
                  (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                  hsummable.of_norm
              have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                  = NumberField.dedekindZeta K s := by
                rw [hzeta,
                  ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                exact tsum_congr hval
              exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
              fun I ↦ (Complex.norm_natCast_cpow_of_pos
                (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
            (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
              (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
            fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
          {x | (x.1 : Ideal (𝓞 K)) ∈ S},
        ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
        ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
      rfl) hdisjR hs1, hD]
    exact (show ∀ {S : Set (Ideal (𝓞 K))}, (∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) → ∀ s : ℝ, primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s from by
      intro S hS s
      let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
        Equiv.subtypeEquivRight fun 𝔭 ↦
          ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
      rw [primeIdealZetaSum, primeIdealZetaSum,
        ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
      rfl) hcover s
  rw [← Finset.sum_div, hsum]
  field_simp
  linarith [hadd]

/-- Pure real-analysis glue: a finite family `gᵢ` of functions, each with
`liminf gᵢ ≥ 1/N` (where `N` is the family size) and bounded below, whose sum
tends to `1`, must each tend to `1/N`. (The lower bounds and the sum-limit pin
every `gᵢ` to `1/N` by a pigeonhole on `liminf`/`limsup`.)

The below-boundedness hypothesis `hbelow` is genuinely needed: a finite `liminf`
lower bound alone does not force below-boundedness in a conditionally complete
order, so without it the statement is false (one `gᵢ` could dip to `-∞` while
keeping a spurious `liminf` and the sum still converging). At the only call site
(`chebotarev_abelian`) each `gᵢ` is a ratio of nonnegative Dirichlet sums, hence
`0 ≤ gᵢ`, so `hbelow` is immediate. -/
theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one {ι : Type*} [Fintype ι]
    {γ : Type*} {l : Filter γ} [l.NeBot] (g : ι → γ → ℝ)
    (hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) l)
    (hbelow : ∀ i, Filter.IsBoundedUnder (· ≥ ·) l (g i))
    (hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) l (𝓝 (1 : ℝ))) (i₀ : ι) :
    Filter.Tendsto (g i₀) l (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  classical
  set N : ℕ := Fintype.card ι with hN
  set F : γ → ℝ := fun s ↦ ∑ i, g i s with hF
  have hFle : l.IsBoundedUnder (· ≤ ·) F := hsum.isBoundedUnder_le
  have hFlimsup : limsup F l = 1 := hsum.limsup_eq
  have hgle : ∀ i, l.IsBoundedUnder (· ≤ ·) (g i) :=
    (show ∀ {l : Filter γ} (g : ι → γ → ℝ) (hF : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ i, g i s)) (hbelow : ∀ i, l.IsBoundedUnder (· ≥ ·) (g i)) (i : ι), (l.IsBoundedUnder (· ≤ ·) (g i)) from by
      intro l g hF hbelow i
      classical
      classical
      obtain ⟨a, ha⟩ := hF.eventually_le
      obtain ⟨b, hb⟩ := (Finset.sum_fn _ g ▸
        Filter.isBoundedUnder_ge_sum (Finset.univ.erase i) (fun j _ ↦ hbelow j)).eventually_ge
      refine isBoundedUnder_of_eventually_le (a := a - b) ?_
      filter_upwards [ha, hb] with s hsa hsb
      have := Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i)
      linarith) g hFle hbelow
  haveI : Nonempty ι := ⟨i₀⟩
  have hNpos : 0 < N := Fintype.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hrestge : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_ge_sum t (fun j _ ↦ hbelow j)
  have hrestle : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_le_sum t (fun j _ ↦ hgle j)
  have hcard : t.card = N - 1 := Finset.card_erase_of_mem (Finset.mem_univ i₀)
  have hliminf_rest : ((N : ℝ) - 1) / N ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l := by
    have hsuper : ∑ j ∈ t, liminf (g j) l ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l := by
      induction t using Finset.induction with
      | empty => simp
      | insert a u ha ih =>
          rw [Finset.sum_insert ha]
          have hbU : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ u, g j s) :=
            Finset.sum_fn u g ▸ Filter.isBoundedUnder_ge_sum u (fun j _ ↦ hbelow j)
          have haU : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ j ∈ u, g j s) :=
            Finset.sum_fn u g ▸ Filter.isBoundedUnder_le_sum u (fun j _ ↦ hgle j)
          have hstep : liminf (g a) l + liminf (fun s ↦ ∑ j ∈ u, g j s) l
              ≤ liminf (fun s ↦ g a s + ∑ j ∈ u, g j s) l :=
            le_liminf_add (hbelow a) (hgle a) hbU
              (IsBoundedUnder.isCoboundedUnder_ge haU)
          calc liminf (g a) l + ∑ j ∈ u, liminf (g j) l
              ≤ liminf (g a) l + liminf (fun s ↦ ∑ j ∈ u, g j s) l := by
                gcongr
            _ ≤ liminf (fun s ↦ g a s + ∑ j ∈ u, g j s) l := hstep
            _ = liminf (fun s ↦ ∑ j ∈ insert a u, g j s) l := by
              simp_rw [Finset.sum_insert ha]
    have hlb : ∑ j ∈ t, ((N : ℝ))⁻¹ ≤ ∑ j ∈ t, liminf (g j) l :=
      Finset.sum_le_sum (fun j _ ↦ hlo j)
    have hconst : ∑ _j ∈ t, ((N : ℝ))⁻¹ = (t.card : ℝ) * (N : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, hcard] at hlb
    have hcast : ((N : ℝ) - 1) / N = ((N - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : (1 : ℕ) ≤ N := hNpos
        push_cast [Nat.cast_sub this]
        ring
      rw [hsub]
      ring
    rw [hcast]
    exact le_trans hlb hsuper
  have hFeq : (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) = F := by
    funext s
    rw [hF]
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i₀)
  have hadd : limsup (g i₀) l + liminf (fun s ↦ ∑ j ∈ t, g j s) l
      ≤ limsup (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) l :=
    le_limsup_add (hgle i₀) (IsBoundedUnder.isCoboundedUnder_le (hbelow i₀)) hrestle hrestge
  rw [hFeq, hFlimsup] at hadd
  have hlimsup_le : limsup (g i₀) l ≤ (N : ℝ)⁻¹ := by
    have hrest_le : liminf (fun s ↦ ∑ j ∈ t, g j s) l ≤ 1 - limsup (g i₀) l := by linarith
    have h1 : limsup (g i₀) l ≤ 1 - ((N : ℝ) - 1) / N := by
      linarith [le_trans hliminf_rest hrest_le]
    have h2 : 1 - ((N : ℝ) - 1) / N = (N : ℝ)⁻¹ := by
      field_simp
      ring
    rwa [h2] at h1
  exact tendsto_of_le_liminf_of_limsup_le (hlo i₀) hlimsup_le (hgle i₀) (hbelow i₀)

/-- **Chebotarev's theorem, abelian case** (Sharifi 7.2.2 Step 2).

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

**Composition**: the `|G|` fibres `S_σ` each have `liminf ≥ 1/|G|`
(`liminf_ratio_ge_inv_card_G`) and their density ratios sum to `1`
(`ratioSum_frobeniusFibres_tendsto_one`); the pigeonhole glue
`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` forces each to the
limit `1/|G|`. -/
theorem chebotarev_abelian
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk τ} s
        / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
    (fun τ ↦ ?_) (fun τ ↦ (show ∀ (T : Set (Ideal (𝓞 K))), (Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ)) (fun s ↦ primeIdealZetaSum T s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)) from by
      intro T
      classical
      exact
        have hnn : ∀ (S : Set (Ideal (𝓞 K))) (s : ℝ), 0 ≤ primeIdealZetaSum S s := fun S s ↦ by
          unfold primeIdealZetaSum
          exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
        isBoundedUnder_of_eventually_ge (a := 0)
          (Filter.Eventually.of_forall fun s ↦ div_nonneg (hnn _ s) (hnn _ s))) _)
    (ratioSum_frobeniusFibres_tendsto_one K L) σ
  simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ

end Chebotarev
