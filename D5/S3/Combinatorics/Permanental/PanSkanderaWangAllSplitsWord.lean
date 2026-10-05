/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Finite permutations are encoded faithfully by one-based words. -/

/- Mathematical classification:
   word: data definition, not a proof declaration.
   ofWord:
     proof_shape: content
     escape_witness: conclusion: bounded word evaluation constructs a bijective Fin map
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.IsPerm
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.PanSkanderaWangBruhat
import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsBruhat

open Finset Equiv
namespace PSW

def word {n : ℕ} (w : Perm (Fin n)) : List ℕ := List.ofFn (fun i => (w i).val + 1)

noncomputable def ofWord {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) : Perm (Fin n) := by
  have ofWord_value_bounds {n : ℕ} {x : List ℕ} (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      1 ≤ x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ∧
      x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ≤ n := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    have hm := hx.subset (List.getElem_mem (l := x) (n := i.val) (by omega))
    simp only [List.mem_range'] at hm
    obtain ⟨j, hj, he⟩ := hm
    omega
  let value : Fin n → Fin n := fun i =>
    ⟨x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) - 1,
      by have hv := ofWord_value_bounds hx i; omega⟩
  refine Equiv.ofBijective value ⟨?_, ?_⟩
  · intro i j hij
    have hvalues : x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) =
        x[j.val]'(by have hh := hx.length_eq; simp at hh; omega) := by
      have he := congrArg Fin.val hij
      have hi := ofWord_value_bounds hx i
      have hj := ofWord_value_bounds hx j
      dsimp [value] at he
      omega
    have hnodup : x.Nodup := hx.nodup_iff.mpr (List.nodup_range' (s := 1) (n := n))
    have hh := hnodup.get_inj_iff.mp hvalues
    exact Fin.ext (congrArg (@Fin.val x.length) hh)
  · intro j
    have hm : j.val + 1 ∈ x := hx.symm.subset (List.mem_range'.mpr ⟨j.val, j.isLt, by omega⟩)
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hin : i < n := by have hl := hx.length_eq; simp at hl; omega
    refine ⟨⟨i, hin⟩, ?_⟩
    apply Fin.ext
    dsimp [value]
    rw [he]
    omega

end PSW
