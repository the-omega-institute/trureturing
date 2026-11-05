/- GID: D5/S3/Topology/LiLiZhaoFiniteCRT
   generality: G
   mirror-B: D5/B/S3/Topology/LiLiZhaoFiniteCRT
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.ChineseRemainder, mathlib/module/Mathlib.Data.Nat.Prime.Nth]
   utility: none
   digest: Finite Chinese-remainder cylinders form the compatibility bridge for the Li–Li–Zhao prime-tail topology construction. -/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sober

open scoped Function BigOperators

namespace D5.S3.Topology.LiLiZhaoFiniteCRT

noncomputable section

/-- The increasing enumeration of the prime numbers. -/
abbrev primeSeq (i : ℕ) : ℕ := Nat.nth Nat.Prime i

lemma primeSeq_prime (i : ℕ) : Nat.Prime (primeSeq i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i

lemma primeSeq_injective : Function.Injective primeSeq :=
  Nat.nth_injective Nat.infinite_setOfPred_prime

lemma primeSeq_coprime {i j : ℕ} (hij : i ≠ j) :
    Nat.Coprime (primeSeq i) (primeSeq j) := by
  exact (Nat.coprime_primes (primeSeq_prime i) (primeSeq_prime j)).2
    (fun h => hij (primeSeq_injective h))

/-- Every finite assignment of residue classes at distinct prime indices is nonempty. -/
theorem finite_crt (s : Finset ℕ) (a : ℕ → ℕ) :
    ∃ x : ℕ, ∀ i ∈ s, x ≡ a i [MOD primeSeq i] := by
  have hne : ∀ i ∈ s, primeSeq i ≠ 0 := fun i _ => (primeSeq_prime i).ne_zero
  have hpair : Set.Pairwise s (Nat.Coprime on primeSeq) := by
    intro i hi j hj hij
    exact primeSeq_coprime hij
  let z := Nat.chineseRemainderOfFinset a primeSeq s hne hpair
  exact ⟨z, z.property⟩

abbrev residue (i a : ℕ) : Set ℕ := {x | x ≡ a [MOD primeSeq i]}

lemma residue_mod (i a : ℕ) : residue i (a % primeSeq i) = residue i a := by
  ext x
  constructor
  · intro h
    exact h.trans (Nat.mod_modEq a (primeSeq i))
  · intro h
    exact h.trans (Nat.mod_modEq a (primeSeq i)).symm

def finiteCylinder (s : Finset ℕ) (a : ℕ → ℕ) : Set ℕ :=
  ⋂ i ∈ s, residue i (a i)

/-- A finite prime-residue cylinder is nonempty. -/
theorem finiteCylinder_nonempty (s : Finset ℕ) (a : ℕ → ℕ) :
    (finiteCylinder s a).Nonempty := by
  obtain ⟨z, hz⟩ := finite_crt s a
  refine ⟨z, ?_⟩
  simpa [finiteCylinder, residue] using hz

/-- Two cylinders supported on disjoint prime indices always meet. -/
theorem disjoint_cylinders_nonempty (s t : Finset ℕ) (hdis : Disjoint s t)
    (a b : ℕ → ℕ) : (finiteCylinder s a ∩ finiteCylinder t b).Nonempty := by
  let u := s ∪ t
  let c : ℕ → ℕ := fun i => if i ∈ s then a i else b i
  obtain ⟨z, hzmem⟩ := finiteCylinder_nonempty u c
  have hz : ∀ i ∈ u, z ≡ c i [MOD primeSeq i] := by
    simpa [finiteCylinder, residue] using hzmem
  have hmem (r : Finset ℕ) (f : ℕ → ℕ) (hr : ∀ i ∈ r, f i = c i)
      (hsub : ∀ i ∈ r, i ∈ u) : z ∈ finiteCylinder r f := by
    simp [finiteCylinder]
    intro i hi
    rw [hr i hi]
    exact hz i (by simp [u, hsub i hi])
  refine ⟨z, hmem s a (fun i hi => by simp [c, hi])
    (fun i hi => Finset.mem_union_left t hi), hmem t b ?_
    (fun i hi => Finset.mem_union_right s hi)⟩
  intro i hi
  have hnot : i ∉ s := by
    intro his
    exact Finset.disjoint_left.1 hdis his hi
  simp [c, hnot]

/-! ### The prime-tail topologies

For `n`, the subbase consists of residue classes for the prime indices at least
`n`.  This is the chain used in the Li--Li--Zhao counterexample.  We keep the
subbase explicit so that later arguments can use the generated-open induction
without committing to a particular choice of representatives.
-/

def tailSubbasis (n : ℕ) : Set (Set ℕ) :=
  {U | ∃ i, n ≤ i ∧ ∃ a, a < primeSeq i ∧ U = residue i a}

def tailTopology (n : ℕ) : TopologicalSpace ℕ :=
  TopologicalSpace.generateFrom (tailSubbasis n)

lemma tailSubbasis_mono {n m : ℕ} (hnm : n ≤ m) :
    tailSubbasis m ⊆ tailSubbasis n := by
  rintro U ⟨i, him, a, ha, rfl⟩
  exact ⟨i, hnm.trans him, a, ha, rfl⟩

/- The chain is decreasing as a family of open-set collections. -/
lemma tailTopology_mono {n m : ℕ} (hnm : n ≤ m) :
    tailTopology n ≤ tailTopology m := by
  exact TopologicalSpace.generateFrom_anti (tailSubbasis_mono hnm)

lemma isOpen_residue_tail {n i a : ℕ} (hin : n ≤ i) (ha : a < primeSeq i) :
    @IsOpen ℕ (tailTopology n) (residue i a) := by
  apply tailTopology_mono hin
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨i, le_rfl, a, ha, rfl⟩

lemma finiteCylinder_isOpen {n : ℕ} (s : Finset ℕ) (a : ℕ → ℕ)
    (hs : ∀ i ∈ s, n ≤ i) (ha : ∀ i ∈ s, a i < primeSeq i) :
    @IsOpen ℕ (tailTopology n) (finiteCylinder s a) := by
  letI : TopologicalSpace ℕ := tailTopology n
  change IsOpen (finiteCylinder s a)
  simp only [finiteCylinder]
  exact isOpen_biInter_finset fun i hi =>
    isOpen_residue_tail (hs i hi) (ha i hi)

lemma finiteCylinder_mem_nhds {n : ℕ} (s : Finset ℕ) (a : ℕ → ℕ) (x : ℕ)
    (hs : ∀ i ∈ s, n ≤ i) (ha : ∀ i ∈ s, a i < primeSeq i)
    (hx : x ∈ finiteCylinder s a) :
    finiteCylinder s a ∈ @nhds ℕ (tailTopology n) x := by
  letI : TopologicalSpace ℕ := tailTopology n
  change finiteCylinder s a ∈ nhds x
  exact (finiteCylinder_isOpen s a hs ha).mem_nhds hx

lemma finiteCylinder_basis_of_generateOpen {n : ℕ} {U : Set ℕ}
    (hU : TopologicalSpace.GenerateOpen (tailSubbasis n) U) (x : ℕ) (hx : x ∈ U) :
    ∃ (s : Finset ℕ) (a : ℕ → ℕ),
      (∀ i ∈ s, n ≤ i) ∧ (∀ i ∈ s, a i < primeSeq i) ∧
        x ∈ finiteCylinder s a ∧ finiteCylinder s a ⊆ U := by
  induction hU generalizing x with
  | basic U hU =>
      rcases hU with ⟨i, hin, a, ha, rfl⟩
      let b : ℕ → ℕ := fun _ => a % primeSeq i
      refine ⟨{i}, b, ?_, ?_, ?_, ?_⟩
      · intro j hj
        have hji : j = i := Finset.mem_singleton.mp hj
        simpa [hji] using hin
      · intro j hj
        have hji : j = i := by simpa using hj
        subst j
        exact Nat.mod_lt _ (primeSeq_prime i).pos
      · have hx' : x ∈ residue i (a % primeSeq i) := by
          rw [residue_mod]
          exact hx
        simpa [finiteCylinder, b] using hx'
      · intro z hz
        have hz' : z ∈ residue i (a % primeSeq i) := by
          simpa [finiteCylinder, b] using hz
        rw [residue_mod] at hz'
        exact hz'
  | univ =>
      refine ⟨∅, fun _ => 0, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp [finiteCylinder]
      · simp [finiteCylinder]
  | @inter U V hU hV ihU ihV =>
      rcases ihU x hx.1 with ⟨s, a, hs, ha, hxs, hsub⟩
      rcases ihV x hx.2 with ⟨t, b, ht, hb, hxt, hsub'⟩
      let u := s ∪ t
      let c : ℕ → ℕ := fun i => if i ∈ s then a i else b i
      have hxs' : ∀ i ∈ s, x ∈ residue i (a i) := by
        simpa [finiteCylinder] using hxs
      have hxt' : ∀ i ∈ t, x ∈ residue i (b i) := by
        simpa [finiteCylinder] using hxt
      refine ⟨u, c, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with his | hit
        · exact hs i his
        · exact ht i hit
      · intro i hi
        rcases Finset.mem_union.mp hi with his | hit
        · simpa [c, his] using ha i his
        · by_cases his : i ∈ s
          · simpa [c, his] using ha i his
          · simpa [c, his] using hb i hit
      · simp [finiteCylinder]
        intro i hi
        rcases Finset.mem_union.mp hi with his | hit
        · simpa [c, his] using hxs' i his
        · by_cases hnot : i ∈ s
          · have hia : a i = b i := by
              apply Nat.ModEq.eq_of_lt_of_lt (m := primeSeq i)
              · exact (hxs' i hnot).symm.trans (hxt' i hit)
              · exact ha i hnot
              · exact hb i hit
            simpa [c, hnot, hia] using hxs' i hnot
          · simpa [c, hnot] using hxt' i hit
      · intro z hz
        have hz' : ∀ i ∈ u, z ∈ residue i (c i) := by
          simpa [finiteCylinder] using hz
        have hz_s : z ∈ finiteCylinder s a := by
          simp [finiteCylinder]
          intro i hi
          have hzu : z ∈ residue i (c i) := by
            exact hz' i (Finset.mem_union_left t hi)
          simpa [c, hi] using hzu
        have hz_t : z ∈ finiteCylinder t b := by
          simp [finiteCylinder]
          intro i hi
          have hzu : z ∈ residue i (c i) := by
            exact hz' i (Finset.mem_union_right s hi)
          by_cases his : i ∈ s
          · have hia : a i = b i := by
              apply Nat.ModEq.eq_of_lt_of_lt (m := primeSeq i)
              · exact (hxs' i his).symm.trans (hxt' i hi)
              · exact ha i his
              · exact hb i hi
            simpa [c, his, hia] using hzu
          · simpa [c, his] using hzu
        exact ⟨hsub hz_s, hsub' hz_t⟩
  | sUnion S hS ih =>
      rcases Set.mem_sUnion.mp hx with ⟨V, hVS, hxV⟩
      rcases ih V hVS x hxV with ⟨s, a, hs, ha, hxs, hsub⟩
      exact ⟨s, a, hs, ha, hxs, fun z hz => Set.subset_sUnion_of_mem hVS (hsub hz)⟩

lemma finiteCylinder_basis_of_isOpen {n : ℕ} {U : Set ℕ}
    (hU : @IsOpen ℕ (tailTopology n) U) (x : ℕ) (hx : x ∈ U) :
    ∃ (s : Finset ℕ) (a : ℕ → ℕ),
      (∀ i ∈ s, n ≤ i) ∧ (∀ i ∈ s, a i < primeSeq i) ∧
        x ∈ finiteCylinder s a ∧ finiteCylinder s a ⊆ U :=
  finiteCylinder_basis_of_generateOpen hU x hx

/- Every tail topology separates two points with one sufficiently large prime. -/
theorem tailTopology_t2 (n : ℕ) : @T2Space ℕ (tailTopology n) := by
  letI : TopologicalSpace ℕ := tailTopology n
  change T2Space ℕ
  apply t2Space_iff_nhds.2
  intro x y hxy
  let i := max n (x + y + 1)
  have hi : x + y < primeSeq i := by
    have hilower : x + y + 1 ≤ i := le_max_right _ _
    have hbound : i + 2 ≤ primeSeq i := by
      exact Nat.add_two_le_nth_prime i
    omega
  have hxlt : x < primeSeq i := lt_of_le_of_lt (Nat.le_add_right x y) hi
  have hylt : y < primeSeq i := lt_of_le_of_lt (Nat.le_add_left y x) hi
  refine ⟨finiteCylinder {i} (fun _ => x), ?_,
    finiteCylinder {i} (fun _ => y), ?_, ?_⟩
  · apply finiteCylinder_mem_nhds {i} (fun _ => x) x
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using le_max_left n (x + y + 1)
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using hxlt
    · simpa [finiteCylinder, residue] using (Nat.ModEq.refl x : x ≡ x [MOD primeSeq i])
  · apply finiteCylinder_mem_nhds {i} (fun _ => y) y
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using le_max_left n (x + y + 1)
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using hylt
    · simpa [finiteCylinder, residue] using (Nat.ModEq.refl y : y ≡ y [MOD primeSeq i])
  · refine Set.disjoint_left.2 ?_
    intro z hzx hzy
    have hzx' : z ≡ x [MOD primeSeq i] := by
      simpa [finiteCylinder, residue] using hzx
    have hzy' : z ≡ y [MOD primeSeq i] := by
      simpa [finiteCylinder, residue] using hzy
    exact hxy (Nat.ModEq.eq_of_lt_of_lt (hzx'.symm.trans hzy') hxlt hylt)

def commonTopology : TopologicalSpace ℕ := ⨆ n, tailTopology n

lemma commonTopology_isOpen_iff {U : Set ℕ} :
    @IsOpen ℕ commonTopology U ↔ ∀ n, @IsOpen ℕ (tailTopology n) U := by
  change @IsOpen ℕ (⨆ n, tailTopology n) U ↔ _
  exact isOpen_iSup_iff

lemma isClosed_singleton_tail (n x : ℕ) :
    @IsClosed ℕ (tailTopology n) ({x} : Set ℕ) := by
  letI : TopologicalSpace ℕ := tailTopology n
  letI : T2Space ℕ := tailTopology_t2 n
  change IsClosed ({x} : Set ℕ)
  exact isClosed_singleton

theorem commonTopology_t1 : @T1Space ℕ commonTopology := by
  letI : TopologicalSpace ℕ := commonTopology
  change T1Space ℕ
  refine ⟨fun x => ?_⟩
  change @IsClosed ℕ (⨆ n, tailTopology n) ({x} : Set ℕ)
  exact isClosed_iSup_iff.2 (fun n => isClosed_singleton_tail n x)

theorem commonTopology_univ_irreducible :
    @IsIrreducible ℕ commonTopology (Set.univ : Set ℕ) := by
  refine ⟨Set.univ_nonempty, ?_⟩
  intro U V hU hV hUn hVn
  rcases hUn with ⟨x, -, hxU⟩
  rcases hVn with ⟨y, -, hyV⟩
  have hU0 : @IsOpen ℕ (tailTopology 0) U := (commonTopology_isOpen_iff.mp hU) 0
  rcases finiteCylinder_basis_of_isOpen hU0 x hxU with
    ⟨s, a, hs, ha, hxs, hsub⟩
  let m := s.sum id + 1
  have hsm : ∀ i ∈ s, i < m := by
    intro i hi
    have hle : i ≤ s.sum id := by
      exact Finset.single_le_sum (f := id)
        (fun _ _ => Nat.zero_le _) hi
    dsimp [m]
    omega
  have hV_m : @IsOpen ℕ (tailTopology m) V := (commonTopology_isOpen_iff.mp hV) m
  rcases finiteCylinder_basis_of_isOpen hV_m y hyV with
    ⟨t, b, ht, hb, hyt, hsub'⟩
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i his hit
    have hle : i < m := hsm i his
    have hge : m ≤ i := ht i hit
    exact (Nat.not_lt_of_ge hge) hle
  obtain ⟨z, hzs, hzt⟩ := disjoint_cylinders_nonempty s t hdis a b
  refine ⟨z, ?_⟩
  exact ⟨by simp, ⟨hsub hzs, hsub' hzt⟩⟩

theorem commonTopology_not_quasiSober :
    ¬ @QuasiSober ℕ commonTopology := by
  letI : TopologicalSpace ℕ := commonTopology
  intro hqs
  letI : QuasiSober ℕ := hqs
  have hirr := commonTopology_univ_irreducible
  obtain ⟨x, hgeneric⟩ := QuasiSober.sober hirr isClosed_univ
  have hsingleton : closure ({x} : Set ℕ) = {x} := by
    letI : T1Space ℕ := commonTopology_t1
    exact (@isClosed_singleton ℕ commonTopology _ x).closure_eq
  have heq : ({x} : Set ℕ) = Set.univ := hsingleton.symm.trans hgeneric.def
  have hne : ({x} : Set ℕ) ≠ Set.univ := by
    intro h
    have := Set.ext_iff.mp h (x + 1)
    simp at this
  exact hne heq

end
end D5.S3.Topology.LiLiZhaoFiniteCRT
