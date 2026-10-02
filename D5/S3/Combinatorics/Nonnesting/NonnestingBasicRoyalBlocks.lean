/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBlocks
   mirror-E: none(waiver:royal-first-order-blocks)
   anchors: []
   utility: none
   digest: Shows that avoiding two ordered triples makes every descent a skew-block cut. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks

theorem descent_separates (p : List ℕ) (hp : p.Nodup)
    (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
    (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
    (t i k : ℕ) (ht : t + 1 < p.length) (hdesc : p[t + 1] < p[t])
    (hi : i ≤ t) (hk : t < k) (hklen : k < p.length) :
    p[k] < p[i] := by
  classical
  have triple_sublist (a b c : ℕ) (u v z : ℕ)
      (hu : u < p.length) (hv : v < p.length) (hz : z < p.length)
      (huv : u < v) (hvz : v < z)
      (ha : p[u] = a) (hb : p[v] = b) (hc : p[z] = c) :
      List.Sublist [a, b, c] p := by
    let f : Fin 3 ↪o Fin p.length :=
      OrderEmbedding.ofMapLEIff
        (fun q => if hq : q.val = 0 then ⟨u, hu⟩ else
          if hq : q.val = 1 then ⟨v, hv⟩ else ⟨z, hz⟩)
        (by intro q r; fin_cases q <;> fin_cases r <;> simp <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f, ?_⟩
    intro q
    fin_cases q <;> simp [f, ha, hb, hc]
  have h132' (u v z : ℕ) (hu : u < p.length) (hv : v < p.length)
      (hz : z < p.length) (huv : u < v) (hvz : v < z)
      (huz : p[u] < p[z]) (hzv : p[z] < p[v]) : False := by
    apply h132; let x : ℕ → ℕ := fun q => if q = 1 then p[u] else if q = 2 then p[z] else p[v]
    refine ⟨x, ?_, ?_, ?_, by simp⟩
    · intro q hq hq'
      have : q = 1 ∨ q = 2 := by simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl
      · simpa [x] using huz
      · simpa [x] using hzv
    · intro q hq hq'
      have : q = 1 ∨ q = 2 ∨ q = 3 := by
        simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl | rfl <;> simp [x, List.getElem_mem]
    · simpa [x] using
        triple_sublist (p[u]) (p[v]) (p[z]) u v z hu hv hz huv hvz rfl rfl rfl
  have h213' (u v z : ℕ) (hu : u < p.length) (hv : v < p.length)
      (hz : z < p.length) (huv : u < v) (hvz : v < z)
      (hvu : p[v] < p[u]) (huz : p[u] < p[z]) : False := by
    apply h213; let x : ℕ → ℕ := fun q => if q = 1 then p[v] else if q = 2 then p[u] else p[z]
    refine ⟨x, ?_, ?_, ?_, by simp⟩
    · intro q hq hq'
      have : q = 1 ∨ q = 2 := by simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl
      · simpa [x] using hvu
      · simpa [x] using huz
    · intro q hq hq'
      have : q = 1 ∨ q = 2 ∨ q = 3 := by
        simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl | rfl <;> simp [x, List.getElem_mem]
    · simpa [x] using
        triple_sublist (p[u]) (p[v]) (p[z]) u v z hu hv hz huv hvz rfl rfl rfl
  have hilen : i < p.length := by omega
  have htlen : t < p.length := by omega
  have hneik : p[i] ≠ p[k] := by
    intro heq; have heq' := (hp.getElem_inj_iff (hi := hilen) (hj := hklen)).mp heq; omega
  have hnetk : p[t] ≠ p[k] := by
    intro heq; have heq' := (hp.getElem_inj_iff (hi := htlen) (hj := hklen)).mp heq; omega
  by_contra hnot
  have hik : p[i] < p[k] := by omega
  by_cases hkt : p[k] < p[t]
  · have hit : i < t := by
      by_contra hni
      have : i = t := by omega
      subst i; omega
    exact (h132' i t k hilen htlen hklen hit hk hik hkt).elim
  · have htk : p[t] < p[k] := by omega
    have htkidx : t + 1 < k := by
      by_contra hni
      have : k = t + 1 := by omega
      subst k; omega
    exact (h213' t (t + 1) k htlen ht hklen (by omega) htkidx
      (by omega) htk).elim
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks.descent_separates
