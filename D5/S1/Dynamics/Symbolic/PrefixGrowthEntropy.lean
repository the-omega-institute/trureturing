/- GID: D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PrefixGrowthEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realized prefix growth equals entropy for nonempty forward-invariant symbolic sets. -/

import D5.S1.Dynamics.Shadowing.MetricTracing
import Mathlib.Analysis.Subadditive
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Tactic

/-!
The new inference identifies the minimal dynamical-cover cardinality with
the number of realized prefixes. Centers may lie in the ambient full shift:
one center still covers only one prefix class, and one actual representative
of each class supplies the reverse bound. Prefix agreement at width k and
horizon n means agreement on n+k-1 coordinates. This exact finite-time
identity is the live escape witness, prior to compilation.

The final theorem has no closedness, surjectivity or shadowing assumption.
It reuses the existing symbolic shift iterate theorem, Mathlib dynamical
covers and uniformity, and Fekete's lemma. Helpers are consumed by the one
public entropy bridge and are not separate proposed library deliveries.
This is the classical symbolic word-growth formula, not a novelty claim.
-/

noncomputable section

open Set Function Filter Dynamics ExpGrowth
open scoped Topology Uniformity ENNReal
open SymbolicDynamics
open D5.S1.Dynamics.Shadowing (shift_one_iterate_apply)

namespace D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy

variable {A : Type*}

/-- The number of actual length-n prefixes, rather than a count of proposed
words or an ambient alphabet bound. -/
def prefixCount (S : Set (ℕ → A)) (n : ℕ) : ℕ :=
  Nat.card (Set.range fun x : S => fun i : Fin n => (x : ℕ → A) i.val)

private abbrev Prefix (S : Set (ℕ → A)) (n : ℕ) :=
  Set.range fun x : S => fun i : Fin n => (x : ℕ → A) i.val

private def realize {S : Set (ℕ → A)} {n : ℕ} (u : Prefix S n) : S :=
  Classical.choose u.property

private theorem realize_eq {S : Set (ℕ → A)} {n : ℕ} (u : Prefix S n) (i : Fin n) :
    (realize u : ℕ → A) i.val = u.val i :=
  congrFun (Classical.choose_spec u.property) i

private def prefixRel (k : ℕ) : SetRel (ℕ → A) (ℕ → A) :=
  {p | ∀ i < k, p.1 i = p.2 i}

private theorem dyn_prefixRel (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    dynEntourage (FullShift.shift (1 : ℕ)) (prefixRel (A := A) k) n =
      prefixRel (n + k - 1) := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [mem_dynEntourage, prefixRel, Set.mem_ofPred_eq, shift_one_iterate_apply]
  constructor
  · intro hp i hi
    by_cases hin : i < n
    · simpa using hp i hin 0 hk
    · have hn1 : n - 1 < n := by omega
      have hj : i - (n - 1) < k := by omega
      have he : n - 1 + (i - (n - 1)) = i := by omega
      simpa only [he] using hp (n - 1) hn1 (i - (n - 1)) hj
  · intro hp t ht j hj
    exact hp (t + j) (by omega)

section FiniteAlphabet

variable [Fintype A]

private theorem count_pos {S : Set (ℕ → A)} (hne : S.Nonempty) (n : ℕ) :
    0 < prefixCount S n := by
  rcases hne with ⟨x, hx⟩
  letI : Nonempty (Prefix S n) :=
    ⟨⟨fun i => x i.val, ⟨⟨x, hx⟩, rfl⟩⟩⟩
  exact Nat.card_pos

private theorem count_le (S : Set (ℕ → A)) (n : ℕ) :
    prefixCount S n ≤ Fintype.card A ^ n := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : Prefix S n → (Fin n → A)) Subtype.val_injective
  simpa only [prefixCount, Prefix, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin] using h

private theorem count_submultiplicative {S : Set (ℕ → A)}
    (hinv : MapsTo (FullShift.shift (1 : ℕ)) S S) :
    Submultiplicative (prefixCount S) := by
  classical
  intro m n
  let split : Prefix S (m + n) → Prefix S m × Prefix S n := fun u =>
    (⟨fun i => u.val (i.castAdd n), ⟨realize u, by
      funext i
      exact realize_eq u (i.castAdd n)⟩⟩,
     ⟨fun j => u.val (j.natAdd m),
       ⟨⟨(FullShift.shift (1 : ℕ))^[m] (realize u),
          hinv.iterate m (realize u).property⟩, by
        funext j
        exact (shift_one_iterate_apply (realize u : ℕ → A) m j.val).trans
          (realize_eq u (j.natAdd m))⟩⟩)
  have hs : Injective split := by
    intro u v huv
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact congrFun (congrArg (fun p : Prefix S m × Prefix S n => p.1.val) huv) j
    · exact congrFun (congrArg (fun p : Prefix S m × Prefix S n => p.2.val) huv) j
  have h := Nat.card_le_card_of_injective split hs
  simpa only [prefixCount, Prefix, Nat.card_prod] using h

private theorem cover_count (S : Set (ℕ → A)) (l : ℕ) :
    (⨅ (s : Finset (ℕ → A))
      (_ : SetRel.IsCover (prefixRel l) S s), (s.card : ℕ∞)) = prefixCount S l := by
  classical
  letI : Fintype (Prefix S l) := Fintype.ofFinite _
  apply le_antisymm
  · let centers : Finset (ℕ → A) :=
      Finset.univ.image (fun u : Prefix S l => (realize u : ℕ → A))
    have hcenters : SetRel.IsCover (prefixRel l) S centers := by
      intro x hx
      let u : Prefix S l := ⟨fun i => x i.val, ⟨⟨x, hx⟩, rfl⟩⟩
      refine ⟨realize u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
      intro i hi
      exact (realize_eq u ⟨i, hi⟩).symm
    refine (iInf₂_le centers hcenters).trans ?_
    exact_mod_cast (show centers.card ≤ prefixCount S l from
      Finset.card_image_le.trans_eq (by simp only [Finset.card_univ, prefixCount,
        Nat.card_eq_fintype_card]))
  · apply le_iInf
    intro centers
    apply le_iInf
    intro hc
    have hpick (u : Prefix S l) :
        ∃ y : centers, (y.val, (realize u : ℕ → A)) ∈ prefixRel l := by
      obtain ⟨y, hy, hyu⟩ := hc (realize u).property
      exact ⟨⟨y, hy⟩, fun i hi => (hyu i hi).symm⟩
    choose pick hpick using hpick
    have hpickinj : Injective pick := by
      intro u v huv
      apply Subtype.ext
      funext i
      calc
        u.val i = (realize u : ℕ → A) i.val := (realize_eq u i).symm
        _ = (pick u).val i.val := (hpick u i.val i.isLt).symm
        _ = (pick v).val i.val := congrArg (fun y : centers => y.val i.val) huv
        _ = (realize v : ℕ → A) i.val := hpick v i.val i.isLt
        _ = v.val i := realize_eq v i
    have h := Nat.card_le_card_of_injective pick hpickinj
    exact_mod_cast (show prefixCount S l ≤ centers.card from by
      simpa only [prefixCount, Prefix, Nat.card_eq_fintype_card, Fintype.card_coe] using h)

private theorem coverMincard_prefixRel (S : Set (ℕ → A)) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) :
    coverMincard (FullShift.shift (1 : ℕ)) S (prefixRel k) n =
      prefixCount S (n + k - 1) := by
  simp only [coverMincard, IsDynCoverOf, dyn_prefixRel k n hk hn]
  exact cover_count S (n + k - 1)

end FiniteAlphabet

section UniformAlphabet

variable [UniformSpace A] [DiscreteUniformity A]

private theorem prefixRel_mem (k : ℕ) : prefixRel (A := A) k ∈ 𝓤 (ℕ → A) := by
  have hi (i : Fin k) : {p : (ℕ → A) × (ℕ → A) | p.1 i.val = p.2 i.val} ∈
      𝓤 (ℕ → A) := by
    simpa only [Filter.mem_map, SetRel.id, Prod.map, Set.mem_ofPred_eq,
      Set.preimage_ofPred_eq] using
      (Pi.uniformContinuous_proj (fun _ : ℕ => A) i.val)
        (DiscreteUniformity.relId_mem_uniformity A)
  have h : (⋂ i : Fin k, {p : (ℕ → A) × (ℕ → A) | p.1 i.val = p.2 i.val}) ∈
      𝓤 (ℕ → A) := Filter.iInter_mem.mpr hi
  apply Filter.mem_of_superset h
  intro p hp i hi
  exact Set.mem_iInter.mp hp ⟨i, hi⟩

private theorem prefixRel_cofinal (U : SetRel (ℕ → A) (ℕ → A)) (hU : U ∈ 𝓤 (ℕ → A)) :
    ∃ k : ℕ, 0 < k ∧ prefixRel k ⊆ U := by
  letI : MetricSpace (ℕ → A) := PiNat.metricSpaceOfDiscreteUniformity
    (fun _ => DiscreteUniformity.eq_principal_setRelId A)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k + 1, by omega, ?_⟩
  intro p hp
  apply hεU
  have hdist : dist p.1 p.2 ≤ (1 / 2 : ℝ) ^ k :=
    PiNat.mem_cylinder_iff_dist_le.mp
      (show p.1 ∈ PiNat.cylinder p.2 k from fun i hi => hp i (by omega))
  exact hdist.trans_lt hk

end UniformAlphabet

/-- The actual prefix counts of every nonempty forward-invariant symbolic
set have a real logarithmic growth limit, equal to its topological entropy.
Closedness, onto dynamics, shadowing and a finite graph presentation are not
assumed. The entropy uses ambient full-shift centers, as in Mathlib. -/
theorem prefix_growth_entropy
    [Fintype A] [UniformSpace A] [DiscreteUniformity A]
    (S : Set (ℕ → A)) (hne : S.Nonempty)
    (hinv : MapsTo (FullShift.shift (1 : ℕ)) S S) :
    ∃ h : ℝ,
      0 ≤ h ∧ h ≤ Real.log (Fintype.card A) ∧
      Tendsto (fun n => Real.log (prefixCount S n : ℝ) / n) atTop (𝓝 h) ∧
      coverEntropy (FullShift.shift (1 : ℕ)) S = (h : EReal) := by
  classical
  have hpos (n : ℕ) : (0 : ℝ) < prefixCount S n := by
    exact_mod_cast count_pos hne n
  have hone (n : ℕ) : (1 : ℝ) ≤ prefixCount S n := by
    exact_mod_cast (count_pos hne n)
  have hsub : Subadditive (fun n => Real.log (prefixCount S n : ℝ)) := by
    intro m n
    calc
      _ ≤ Real.log ((prefixCount S m : ℝ) * prefixCount S n) :=
        Real.log_le_log (hpos _) (by exact_mod_cast count_submultiplicative hinv m n)
      _ = _ := Real.log_mul (hpos _).ne' (hpos _).ne'
  have hbdd : BddBelow (Set.range fun n : ℕ => Real.log (prefixCount S n : ℝ) / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (Real.log_nonneg (hone n)) (Nat.cast_nonneg n)
  let h : ℝ := hsub.lim
  have hlim : Tendsto (fun n => Real.log (prefixCount S n : ℝ) / n) atTop (𝓝 h) :=
    hsub.tendsto_lim hbdd
  have hnonneg : 0 ≤ h := ge_of_tendsto hlim <|
    Eventually.of_forall fun n => div_nonneg (Real.log_nonneg (hone n)) (Nat.cast_nonneg n)
  have hupper : h ≤ Real.log (Fintype.card A) := by
    have hle := hsub.lim_le_div hbdd (n := 1) (by norm_num)
    simp only [Nat.cast_one, div_one] at hle
    exact hle.trans (Real.log_le_log (hpos 1) (by
      exact_mod_cast (show prefixCount S 1 ≤ Fintype.card A from by
        simpa only [pow_one] using count_le S 1)))
  have hshift (r : ℕ) :
      expGrowthSup (fun n => (prefixCount S (n + r) : ℝ≥0∞)) = (h : EReal) := by
    have ht : Tendsto (fun n : ℕ => ((n + r : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      simpa only [Nat.cast_add, zero_add, add_zero, one_mul, div_one, add_comm] using
        (tendsto_add_mul_div_add_mul_atTop_nhds (r : ℝ) 0 1 (d := 1) one_ne_zero)
    have hr : Tendsto (fun n : ℕ => Real.log (prefixCount S (n + r) : ℝ) / n)
        atTop (𝓝 h) := by
      have hh := (hlim.comp (tendsto_add_atTop_nat r)).mul ht
      simp only [mul_one] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hnr : ((n + r : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show n + r ≠ 0 by omega)
      dsimp only [Function.comp_def]
      field_simp [hn0, hnr]
    apply Tendsto.limsup_eq
    refine (EReal.tendsto_coe.mpr hr).congr' ?_
    exact Eventually.of_forall fun n => by
      change ((Real.log (prefixCount S (n + r) : ℝ) / n : ℝ) : EReal) =
        ENNReal.log (prefixCount S (n + r) : ℝ≥0∞) / (n : EReal)
      rw [ENNReal.log_pos_real (by exact_mod_cast (hpos (n + r)).ne') (by simp),
        ENNReal.toReal_natCast]
      simp only [EReal.coe_div, EReal.coe_natCast]
  have hent (k : ℕ) (hk : 0 < k) :
      coverEntropyEntourage (FullShift.shift (1 : ℕ)) S (prefixRel k) = (h : EReal) := by
    unfold coverEntropyEntourage
    calc
      _ = expGrowthSup (fun n => (prefixCount S (n + (k - 1)) : ℝ≥0∞)) := by
        apply expGrowthSup_congr
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [coverMincard_prefixRel S k n hk (by omega)]
        rw [show n + k - 1 = n + (k - 1) by omega, ENat.toENNReal_coe]
      _ = h := hshift (k - 1)
  refine ⟨h, hnonneg, hupper, hlim, le_antisymm ?_ ?_⟩
  · unfold coverEntropy
    apply iSup₂_le
    intro U hU
    obtain ⟨k, hk, hkU⟩ := prefixRel_cofinal U hU
    exact (coverEntropyEntourage_antitone (FullShift.shift (1 : ℕ)) S hkU).trans_eq
      (hent k hk)
  · rw [← hent 1 (by norm_num)]
    exact coverEntropyEntourage_le_coverEntropy _ _ (prefixRel_mem 1)

#print axioms prefix_growth_entropy

end D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
