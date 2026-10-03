/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHooks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHooks
   mirror-E: none(waiver:royal-hook-blocks)
   anchors: []
   utility: none
   digest: Locates the decreasing prefix and lower suffix around a maximum. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHooks

theorem maximum_hook_structure (p : List ℕ) (hp : p.Nodup)
    (h123 : ¬ NonnestingDefs.Occurs [1, 2, 3] p)
    (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
    (m : ℕ) (hm : m < p.length)
    (hmax : ∀ k (hk : k < p.length), k ≠ m → p[k] < p[m]) :
    (∀ i j (hi : i < p.length) (hj : j < p.length),
      i < j → j < m → p[j] < p[i]) ∧
    (∀ i k (hi : i < p.length) (hk : k < p.length),
      i < m → m < k → p[k] < p[i]) := by
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
  have hne (u v : ℕ) (hu : u < p.length) (hv : v < p.length)
      (huv : u < v) : p[u] ≠ p[v] := by
    intro heq; have := (hp.getElem_inj_iff (hi := hu) (hj := hv)).mp heq; omega
  constructor
  · intro i j hi hj hij hjm
    by_contra hnot
    have hijv : p[i] < p[j] := by
      have := hne i j hi hj hij; omega
    have hjmax : p[j] < p[m] := hmax j hj (by omega); apply h123
    let x : ℕ → ℕ := fun q => if q = 1 then p[i] else if q = 2 then p[j] else p[m]
    refine ⟨x, ?_, ?_, ?_, by simp⟩
    · intro q hq hq'
      have : q = 1 ∨ q = 2 := by simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl
      · simpa [x] using hijv
      · simpa [x] using hjmax
    · intro q hq hq'
      have : q = 1 ∨ q = 2 ∨ q = 3 := by
        simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl | rfl <;> simp [x, List.getElem_mem]
    · simpa [x] using
        triple_sublist (p[i]) (p[j]) (p[m]) i j m hi hj hm hij hjm rfl rfl rfl
  · intro i k hi hk him hmk
    by_contra hnot
    have hikv : p[i] < p[k] := by
      have := hne i k hi hk (by omega); omega
    have hkmax : p[k] < p[m] := hmax k hk (by omega); apply h132
    let x : ℕ → ℕ := fun q => if q = 1 then p[i] else if q = 2 then p[k] else p[m]
    refine ⟨x, ?_, ?_, ?_, by simp⟩
    · intro q hq hq'
      have : q = 1 ∨ q = 2 := by simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl
      · simpa [x] using hikv
      · simpa [x] using hkmax
    · intro q hq hq'
      have : q = 1 ∨ q = 2 ∨ q = 3 := by
        simp [NonnestingDefs.letters] at hq'; omega
      rcases this with rfl | rfl | rfl <;> simp [x, List.getElem_mem]
    · simpa [x] using
        triple_sublist (p[i]) (p[m]) (p[k]) i m k hi hm hk him hmk rfl rfl rfl
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHooks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHooks.maximum_hook_structure
