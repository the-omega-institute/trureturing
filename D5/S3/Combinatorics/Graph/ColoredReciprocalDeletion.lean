/- GID: D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ColoredReciprocalDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Private monochromatic neighborhoods pay weighted induced-deletion deficits. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex sees two different colors in its neighborhood. -/
def Mixed (G : SimpleGraph V) (c : V → Fin 3) (w : V) : Prop :=
  ∃ r s, G.Adj w r ∧ G.Adj w s ∧ c r ≠ c s

/-- The rational reciprocal potential, including empty color classes. -/
def potential (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 3) : ℚ :=
  (∑ i : Fin 3, 1 / ((univ.filter fun v => c v = i).card + 1 : ℚ)) +
    (1 / 2 : ℚ) * ∑ v, 1 / (G.degree v + 1 : ℚ)

/-- The deficit of a degree-two vertex, expressed without choosing an order on its neighbors. -/
def debt (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) : ℚ :=
  1 / 6 - (1 / 2 : ℚ) * ∑ v ∈ G.neighborFinset w, 1 / (G.degree v + 1 : ℚ)

open Classical in
/-- Simultaneous induced deletion pays the sum of all selected positive deficits. -/
theorem weighted_induced_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 3))
    (W : Finset V)
    (hmixed : ∀ w ∈ W, Mixed G c w)
    (hdegree : ∀ w ∈ W, G.degree w = 2)
    (hprivate : ∀ w ∈ W, ∀ v, G.Adj w v →
      ¬ Mixed G c v ∧ ∀ u, G.Adj v u → Mixed G c u → u = w)
    (hpositive : ∀ w ∈ W, 0 < debt G w) :
    (∑ w ∈ W, debt G w) ≤ potential G c -
      potential (G.induce {v | v ∉ W}) (fun v => c v.val) := by
  classical
  let N (v : V) := G.neighborFinset v
  let P (S : Finset V) : ℚ :=
    (∑ i : Fin 3, 1 / ((S.filter fun v => c v = i).card + 1 : ℚ)) +
      (1 / 2 : ℚ) * ∑ v ∈ S, 1 / ((N v ∩ S).card + 1 : ℚ)
  have hpair (w : V) (hw : w ∈ W) :
      ∃ r s, r ≠ s ∧ N w = {r, s} := by
    apply card_eq_two.mp
    simpa [N] using hdegree w hw
  have hkeep (T : Finset V) (hT : T ⊆ W) (w : V) (hw : w ∈ W)
      (hwt : w ∉ T) : N w ⊆ univ \ T ∧
      ∀ v ∈ N w, N v ⊆ univ \ T := by
    constructor
    · intro v hv
      simp only [mem_sdiff, mem_univ, true_and]
      intro hvT
      exact (hprivate w hw v ((G.mem_neighborFinset _ _).mp hv)).1
        (hmixed v (hT hvT))
    · intro v hv u hu
      simp only [mem_sdiff, mem_univ, true_and]
      intro huT
      have he := (hprivate w hw v ((G.mem_neighborFinset _ _).mp hv)).2 u
        ((G.mem_neighborFinset _ _).mp hu) (hmixed u (hT huT))
      exact hwt (he ▸ huT)
  have step (S : Finset V) (w : V) (hw : w ∈ W) (hws : w ∈ S)
      (hk : N w ⊆ S) (hk' : ∀ v ∈ N w, N v ⊆ S) :
      debt G w + P (S.erase w) ≤ P S := by
    obtain ⟨r, s, hrs, hns⟩ := hpair w hw
    have hr : G.Adj w r := (G.mem_neighborFinset _ _).mp (by change r ∈ N w; rw [hns]; simp)
    have hs : G.Adj w s := (G.mem_neighborFinset _ _).mp (by change s ∈ N w; rw [hns]; simp)
    have hrw : r ≠ w := hr.ne.symm
    have hsw : s ≠ w := hs.ne.symm
    have hrS : r ∈ S := hk (by rw [hns]; simp)
    have hsS : s ∈ S := hk (by rw [hns]; simp)
    have hkr : N r ⊆ S := hk' r (by rw [hns]; simp)
    have hks : N s ⊆ S := hk' s (by rw [hns]; simp)
    have hNw : (N w ∩ S).card = 2 := by
      rw [inter_eq_left.mpr hk, hns]
      simp [hrs]
    have hNr : (N r ∩ S).card = G.degree r := by
      rw [inter_eq_left.mpr hkr]
      exact G.card_neighborFinset_eq_degree r
    have hNs : (N s ∩ S).card = G.degree s := by
      rw [inter_eq_left.mpr hks]
      exact G.card_neighborFinset_eq_degree s
    have hd : debt G w = 1 / 6 - (1 / 2 : ℚ) *
        (1 / (G.degree r + 1 : ℚ) + 1 / (G.degree s + 1 : ℚ)) := by
      unfold debt
      change 1 / 6 - (1 / 2 : ℚ) * (∑ v ∈ N w, 1 / (G.degree v + 1 : ℚ)) = _
      rw [hns]
      simp [hrs]
    have hp := hpositive w hw
    rw [hd] at hp
    have dr0 : (0 : ℚ) < G.degree r + 1 := by positivity
    have ds0 : (0 : ℚ) < G.degree s + 1 := by positivity
    have hdr : 2 ≤ G.degree r := by
      have hh : (1 : ℚ) / (G.degree r + 1) < 1 / 3 := by
        have := le_of_lt (one_div_pos.mpr ds0)
        linarith
      have hh' := (div_lt_div_iff₀ dr0 (by norm_num : (0 : ℚ) < 3)).mp hh
      exact_mod_cast (show (2 : ℚ) ≤ G.degree r by linarith)
    have hds : 2 ≤ G.degree s := by
      have hh : (1 : ℚ) / (G.degree s + 1) < 1 / 3 := by
        have := le_of_lt (one_div_pos.mpr dr0)
        linarith
      have hh' := (div_lt_div_iff₀ ds0 (by norm_num : (0 : ℚ) < 3)).mp hh
      exact_mod_cast (show (2 : ℚ) ≤ G.degree s by linarith)
    let n := (S.filter fun v => c v = c w).card
    have hcolor (v : V) (hv : G.Adj w v) :
        N v ⊆ S.filter (fun u => c u = c w) := by
      intro u hu
      refine mem_filter.mpr ⟨hk' v ((G.mem_neighborFinset _ _).mpr hv) hu, ?_⟩
      by_contra hne
      exact (hprivate w hw v hv).1
        ⟨u, w, (G.mem_neighborFinset _ _).mp hu, hv.symm, hne⟩
    have hrn : G.degree r ≤ n := by
      simpa [n, N] using card_le_card (hcolor r hr)
    have hsn : G.degree s ≤ n := by
      simpa [n, N] using card_le_card (hcolor s hs)
    have hn : 0 < n := by omega
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn
    have arithmetic (d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n) :
        (1 : ℚ) / d + 1 / ((n : ℚ) * (n + 1)) ≤ 2 / (d + 1) := by
      have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      have hd2q : (2 : ℚ) ≤ d := by exact_mod_cast hd2
      have hdnq : (d : ℚ) ≤ n := by exact_mod_cast hdn
      have hmono : (1 : ℚ) / ((n : ℚ) * (n + 1)) ≤
          1 / ((d : ℚ) * (d + 1)) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have hsmall : (1 : ℚ) / d + 1 / ((d : ℚ) * (d + 1)) ≤ 2 / (d + 1) := by
        apply (le_of_mul_le_mul_right ?_ (show (0 : ℚ) < d * (d + 1) by positivity))
        field_simp
        nlinarith
      linarith only [hmono, hsmall]
    have har := arithmetic (G.degree r) hdr hrn
    have has := arithmetic (G.degree s) hds hsn
    have hinter (v : V) : N v ∩ S.erase w = (N v ∩ S).erase w := by
      ext u
      simp only [mem_inter, mem_erase]
      tauto
    have hafter (v : V) (hv : v ∈ S.erase w) :
        (1 : ℚ) / ((N v ∩ S.erase w).card + 1) =
          1 / ((N v ∩ S).card + 1) +
          (if v = r then 1 / (G.degree r : ℚ) - 1 / (G.degree r + 1 : ℚ) else 0) +
          (if v = s then 1 / (G.degree s : ℚ) - 1 / (G.degree s + 1 : ℚ) else 0) := by
      rw [hinter]
      by_cases hvr : v = r
      · subst v
        have hm : w ∈ N r ∩ S := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hr.symm, hws⟩
        have hc := card_erase_add_one hm
        rw [hNr] at hc
        have hcq : (((N r ∩ S).erase w).card : ℚ) + 1 = G.degree r := by exact_mod_cast hc
        simp only [hNr, hcq, ite_true, if_neg hrs]
        ring
      · by_cases hvs : v = s
        · subst v
          have hm : w ∈ N s ∩ S := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hs.symm, hws⟩
          have hc := card_erase_add_one hm
          rw [hNs] at hc
          have hcq : (((N s ∩ S).erase w).card : ℚ) + 1 = G.degree s := by exact_mod_cast hc
          simp only [hNs, hcq, if_neg hvr, ite_true]
          ring
        · have hnot : w ∉ N v ∩ S := by
            intro hh
            have hvN : v ∈ N w := (G.mem_neighborFinset _ _).mpr
              ((G.mem_neighborFinset _ _).mp (mem_inter.mp hh).1).symm
            rw [hns] at hvN
            simp only [mem_insert, mem_singleton] at hvN
            exact hvN.elim hvr hvs
          simp [erase_eq_of_notMem hnot, hvr, hvs]
    have hvsum : (∑ v ∈ S.erase w, (1 : ℚ) / ((N v ∩ S.erase w).card + 1)) =
        (∑ v ∈ S, (1 : ℚ) / ((N v ∩ S).card + 1)) - 1 / 3 +
        (1 / (G.degree r : ℚ) - 1 / (G.degree r + 1 : ℚ)) +
        (1 / (G.degree s : ℚ) - 1 / (G.degree s + 1 : ℚ)) := by
      rw [sum_congr rfl hafter, sum_add_distrib, sum_add_distrib]
      have he := sum_erase_add S (fun v => (1 : ℚ) / ((N v ∩ S).card + 1)) hws
      rw [hNw] at he
      simp only [Nat.cast_ofNat] at he
      have hrE : r ∈ S.erase w := mem_erase.mpr ⟨hrw, hrS⟩
      have hsE : s ∈ S.erase w := mem_erase.mpr ⟨hsw, hsS⟩
      simp only [sum_ite_eq', hrE, hsE, if_true]
      linarith
    have hcafter (i : Fin 3) :
        (1 : ℚ) / (((S.erase w).filter fun v => c v = i).card + 1) =
          1 / ((S.filter fun v => c v = i).card + 1) +
          if i = c w then 1 / (n : ℚ) - 1 / (n + 1 : ℚ) else 0 := by
      have hfilter : (S.erase w).filter (fun v => c v = i) =
          (S.filter fun v => c v = i).erase w := by ext v; simp [and_assoc]
      rw [hfilter]
      by_cases hi : i = c w
      · subst i
        have hc := card_erase_add_one
          (mem_filter.mpr ⟨hws, rfl⟩ : w ∈ S.filter (fun v => c v = c w))
        have hcq : (((S.filter fun v => c v = c w).erase w).card : ℚ) + 1 = n := by
          exact_mod_cast hc
        simp only [hcq, ite_true]
        change 1 / (n : ℚ) = 1 / (n + 1 : ℚ) + (1 / (n : ℚ) - 1 / (n + 1 : ℚ))
        ring
      · have hnot : w ∉ S.filter (fun v => c v = i) := by simp [Ne.symm hi]
        simp [erase_eq_of_notMem hnot, hi]
    have hcsum : (∑ i : Fin 3, (1 : ℚ) / (((S.erase w).filter fun v => c v = i).card + 1)) =
        (∑ i : Fin 3, (1 : ℚ) / ((S.filter fun v => c v = i).card + 1)) +
          (1 / (n : ℚ) - 1 / (n + 1 : ℚ)) := by
      simp_rw [hcafter]
      simp [sum_add_distrib]
    have hfrac : (1 : ℚ) / n - 1 / (n + 1 : ℚ) = 1 / ((n : ℚ) * (n + 1)) := by
      field_simp
      ring
    dsimp only [P]
    rw [hvsum, hcsum, hfrac, hd]
    simp only [div_eq_mul_inv] at har has ⊢
    linarith only [har, has]
  have telescope (T : Finset V) (hT : T ⊆ W) :
      (∑ w ∈ T, debt G w) + P (univ \ T) ≤ P univ := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert w T hwt ih =>
      have hw : w ∈ W := hT (mem_insert_self _ _)
      have hTW : T ⊆ W := (subset_insert _ _).trans hT
      have hkeepT := hkeep T hTW w hw hwt
      have hs := step (univ \ T) w hw (by simp [hwt]) hkeepT.1 hkeepT.2
      have he : univ \ insert w T = (univ \ T).erase w := by ext v; simp
      rw [sum_insert hwt, he]
      linarith [ih hTW]
  have hP (S : Set V) [Fintype S] :
      P S.toFinset = potential (G.induce S) (fun v => c v.val) := by
    have hdegrees (v : S) (F : Fintype ((G.induce S).neighborSet v)) :
        @SimpleGraph.degree _ (G.induce S) v F = (N v.val ∩ S.toFinset).card := by
      have hh := congrArg Finset.card (G.map_neighborFinset_induce v)
      simp only [card_map] at hh
      convert hh using 1 <;> congr 2
      · exact Subsingleton.elim _ _
      · ext u; simp
    have hcards (i : Fin 3) :
        (univ.filter fun v : S => c v.val = i).card =
          (S.toFinset.filter fun v => c v = i).card := by
      apply card_bij (fun v _ => v.val)
      · intro v hv; exact mem_filter.mpr ⟨by simp, (mem_filter.mp hv).2⟩
      · intro v _ u _ h; exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v, by simpa using (mem_filter.mp hv).1⟩,
          by simpa using (mem_filter.mp hv).2, rfl⟩
    simp only [potential, hcards, hdegrees]
    dsimp only [P]
    congr 1
    congr 1
    exact sum_subtype S.toFinset (fun v => Set.mem_toFinset)
      (fun v => (1 : ℚ) / ((N v ∩ S.toFinset).card + 1))
  have hPU : P univ = potential G c := by simp [P, potential, N]
  have hPW : P (univ \ W) = potential (G.induce {v | v ∉ W}) (fun v => c v.val) := by
    have he : ({v | v ∉ W} : Set V).toFinset = univ \ W := by ext v; simp
    simpa only [he] using hP {v | v ∉ W}
  have ht := telescope W subset_rfl
  rw [hPU, hPW] at ht
  linarith

end D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion
