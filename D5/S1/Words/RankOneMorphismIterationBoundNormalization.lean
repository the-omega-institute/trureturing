/- GID: D5/S1/Words/RankOneMorphismIterationBoundNormalization
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundNormalization
   mirror-E: none(waiver:consumed-source-normalization)
   anchors: []
   digest: Original four-word witness iff exact gcd-spaced finite prefix samples. -/
import D5.S1.Words.RankOneMorphismIterationBoundCyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem charge_rotation_before (u v : Word) (i : ℕ) (hi : i ≤ u.length) :
    p.charge ((v++u).take (v.length+i)) = p.charge v + p.charge ((u++v).take i) := by
  rw [List.take_append, List.take_of_length_le (by omega : v.length ≤ v.length+i),
    Nat.add_sub_cancel_left, p.charge_append, List.take_append_of_le_length hi]

theorem charge_rotation_after (u v : Word) (i : ℕ)
    (hi : u.length ≤ i) (hi' : i ≤ (u++v).length) :
    p.charge ((v++u).take (i-u.length)) = p.charge ((u++v).take i) - p.charge u := by
  rw [List.take_append_of_le_length (by simp only [List.length_append] at hi'; omega)]
  rw [List.take_append, List.take_of_length_le hi, p.charge_append]
  ring

/-- Homogeneous blocks give every boundary at every multiple of a grouped length. -/
theorem homogeneous_boundaries {w : Word} {V : Letter → ℕ} {P : ℕ}
    (hw : p.charge w = 0) (hb : Blocks w V) (hd : (V 0+V 1) ∣ P) :
    ∀ j, j*P ≤ w.length → p.charge (w.take (j*P)) = 0 := by
  obtain ⟨bs, hflat, hn, hc⟩ := p.block_charge_zero hw hb
  have hsame (xs : List Word) (hs : ∀ b ∈ xs, b.length = V 0+V 1) :
      xs.flatten.length = xs.length*(V 0+V 1) := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [hs b (by simp), ih (by intro b hb; exact hs b (by simp [hb]))]
      ring
  have hlen : w.length = bs.length*(V 0+V 1) := by
    rw [← hflat]; exact hsame bs (fun b hb => (hc b hb).2.1)
  have hL : 0 < V 0+V 1 := by
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil bs hn
    have h := hc b hb
    have hpos := List.length_pos_iff.mpr h.1
    rw [h.2.1] at hpos
    exact hpos
  obtain ⟨k, hk⟩ := hd
  intro j hj
  have hidx : j*k ≤ bs.length := by rw [hk] at hj; nlinarith
  have hz := p.zero_block_boundaries bs (V 0+V 1) (fun b hb => (hc b hb).2) (j*k) hidx
  rw [hflat] at hz
  have he : j*P = (j*k)*(V 0+V 1) := by rw [hk]; ring
  rwa [he]

/-- A cyclic cut is reduced modulo the gcd-length without deleting endpoint
    cuts or the one-block cases. -/
theorem rebase_samples (u v : Word) (n P : ℕ) (hP : 0 < P)
    (hl : (u++v).length = n*P) (hz : p.charge (u++v) = 0)
    (hb : ∀ j, j*P ≤ (v++u).length → p.charge ((v++u).take (j*P)) = 0) :
    ∀ j, j < n → p.charge ((u++v).take (u.length%P+j*P)) = p.charge u := by
  intro j hj
  let q := u.length/P
  let r := u.length%P
  have he : q*P+r = u.length := by exact Nat.div_add_mod' _ _
  have hr : r < P := Nat.mod_lt _ hP
  have hq : q ≤ n := by simp only [List.length_append] at hl; nlinarith
  have hi : r+j*P ≤ (u++v).length := by nlinarith
  change p.charge ((u++v).take (r+j*P)) = p.charge u
  by_cases hqj : q ≤ j
  · have hdiff := Nat.sub_add_cancel hqj
    have hge : u.length ≤ r+j*P := by nlinarith
    have hdelta : (j-q)*P = r+j*P-u.length := by nlinarith [Nat.sub_add_cancel hge]
    have hz' := hb (j-q) (by simp only [List.length_append] at *; nlinarith)
    rw [hdelta, p.charge_rotation_after u v _ hge hi] at hz'
    omega
  · have hjq : j < q := by omega
    have hbefore : r+j*P ≤ u.length := by nlinarith
    have hdiff := Nat.sub_add_cancel (show q ≤ n+j by omega)
    have hdelta : (n+j-q)*P = v.length+(r+j*P) := by
      simp only [List.length_append] at hl
      nlinarith
    have hz' := hb (n+j-q) (by rw [hdelta]; simp only [List.length_append]; omega)
    rw [hdelta, p.charge_rotation_before u v _ hbefore] at hz'
    rw [p.charge_append] at hz
    omega

theorem blocks_length_divides {w : Word} {V : Letter → ℕ} (h : Blocks w V) :
    (V 0+V 1) ∣ w.length := by
  obtain ⟨bs, hb, hn, hv⟩ := h
  rw [← hb, length_flatten_constant bs V (fun b hb => (hv b hb).2)]
  exact dvd_mul_left _ _

/-- Every actual source witness normalizes to one common charge on all gcd cuts. -/
theorem original_to_samples {t : ℕ} (h : OriginalCyclicBlockWitness f (t+1)) :
    p.CutSamples t := by
  obtain ⟨u,v,u',v',ha,hb,hab,V,hblocksA,hblocksB⟩ := h
  let P := p.d*p.lam^t
  have hP : 0 < P := Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
  have hd : (V 0+V 1) ∣ P := by
    have hda := blocks_length_divides hblocksA
    have hdb := blocks_length_divides hblocksB
    have hla : (v++u).length = (image f (t+1) 0).length := by rw [ha]; simp only [List.length_append]; omega
    have hlb : (v'++u').length = (image f (t+1) 1).length := by rw [hb]; simp only [List.length_append]; omega
    rw [hla] at hda; rw [hlb] at hdb
    change (V 0+V 1) ∣ p.d*p.lam^t
    rw [← p.iterated_gcd]
    exact Nat.dvd_gcd hda hdb
  have hlen := abelianEq_length hab
  have hcharge := (p.charge_eq_iff hlen).mpr hab
  refine ⟨u.length%P, Nat.mod_lt _ hP, p.charge u, ?_⟩
  intro c j hj
  have hzi (c : Letter) : p.charge (image f (t+1) c) = 0 := by simp
  fin_cases c
  · change p.charge ((image f (t+1) 0).take (u.length%P+j*P)) = p.charge u
    rw [ha]
    apply p.rebase_samples u v p.n P hP
    · simpa only [ha, P, mult, ite_true] using p.iterated_length t 0
    · simpa only [ha] using hzi 0
    · apply p.homogeneous_boundaries (P := P) _ hblocksA hd
      have hz := hzi 0
      rw [ha, p.charge_append] at hz
      rw [p.charge_append]; omega
    · simpa [mult] using hj
  · change p.charge ((image f (t+1) 1).take (u.length%P+j*P)) = p.charge u
    rw [hb]
    rw [hcharge, hlen]
    apply p.rebase_samples u' v' p.m P hP
    · simpa only [hb, P, mult, show (1 : Letter) ≠ 0 by decide, ite_false] using p.iterated_length t 1
    · simpa only [hb] using hzi 1
    · apply p.homogeneous_boundaries (P := P) _ hblocksB hd
      simp only [p.charge_append] at *
      have hz := hzi 1
      rw [hb, p.charge_append] at hz
      omega
    · simpa [mult] using hj

/-- Equal finite sampled charges reconstruct both complete normalized rotations. -/
theorem samples_to_normalized {t : ℕ} (h : p.CutSamples t) : p.NormalizedWitness t := by
  obtain ⟨r, hr, Z, hs⟩ := h
  let P := p.d*p.lam^t
  have hP : 0 < P := Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _)
  have hm (c : Letter) : 0 < p.mult c := by fin_cases c <;> simp [mult, p.n_pos, p.m_pos]
  have hlen (c : Letter) : r ≤ (image f (t+1) c).length := by
    rw [p.iterated_length]; have := hm c; nlinarith
  have h0 (c : Letter) : p.charge ((image f (t+1) c).take r) = Z := by
    simpa using hs c 0 (hm c)
  refine ⟨r, hr, (p.charge_eq_iff ?_).mp ((h0 0).trans (h0 1).symm), ?_⟩
  · simp only [List.length_take, Nat.min_eq_left (hlen 0), Nat.min_eq_left (hlen 1)]
  · intro c
    let w := image f (t+1) c
    have hwlen : w.length = p.mult c*P := p.iterated_length t c
    have hrotlen : (w.drop r++w.take r).length = p.mult c*P := by
      simp only [List.length_append, List.length_drop, List.length_take,
        Nat.min_eq_left (hlen c)]
      omega
    apply p.blocks_of_boundaries t (p.mult c) _ (hm c) hrotlen
    intro j hj
    by_cases hjlast : j = p.mult c
    · rw [hjlast, ← hrotlen, List.take_length, p.charge_append]
      have hwhole : p.charge w = 0 := by simp [w]
      have hdecomp := congrArg p.charge (List.take_append_drop r w)
      rw [p.charge_append] at hdecomp
      omega
    · have hj' : j < p.mult c := by omega
      have hcut : j*P ≤ (w.drop r).length := by
        simp only [List.length_drop]
        have hrP : r < P := hr
        have hwr : r ≤ w.length := hlen c
        have hsub := Nat.sub_add_cancel hwr
        nlinarith
      rw [List.take_append_of_le_length hcut]
      have h := p.charge_take_add w r (j*P)
      have hsample : p.charge (w.take (r+j*P)) = Z := hs c j hj'
      have hstart : p.charge (w.take r) = Z := h0 c
      rw [hsample, hstart] at h
      omega

/-- Source-faithful finite normalization; all four words and entire blocks
    remain in the theorem's original witness predicate. -/
theorem original_iff_samples (t : ℕ) :
    OriginalCyclicBlockWitness f (t+1) ↔ p.CutSamples t := by
  exact ⟨p.original_to_samples, fun h => p.normalized_original (p.samples_to_normalized h)⟩


end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
