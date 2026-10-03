/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/SumRules
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
unsigned_moment_open:
  proof_shape: content
  escape_witness: finiteSixJ_action: the actual normalized six-j matrix intertwines finiteSixJJacobi with its spin-Casimir diagonal. Together with the constructed physicalU orthogonality it evaluates the central Jacobi diagonal, not just a bound.
result:
  proof_shape: content
  escape_witness: inverse_moment_open: the full weighted inverse-Casimir W-square sum equals 1/(N*abs(j-l)*(j+l+1)) for 1<=j,l<N and j!=l. This constructed scalar identity is a live conjunct of claim; the other live content paths are alternating_moment_open, unsigned_moment_open and binomial_harmonic via the Racah expansion.
admission_basis: open-problem-resolution (#11604; Proved)
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Alternating
import Mathlib.Algebra.BigOperators.Field

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Alternating

private theorem unsigned_moment_open (N j l : ℕ) (hN : 2 ≤ N)
    (hj : 1 ≤ j ∧ j < N) (hl : 1 ≤ l ∧ l < N) :
    (∑ i ∈ range (N-1), casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
      W N (i+1) j l ^ 2) =
      (((N : ℝ)^2-1)*(casimir j+casimir l)-2*casimir j*casimir l)/
        ((N : ℝ)*((N : ℝ)^2-1)) := by
  have sum_shifted_support (f : ℕ → ℝ) (n r d : ℕ) (hd : d≤r) (hr : r≤n)
      (hz : ∀ i, i < d ∨ r < i → f i=0) :
      (∑ t ∈ range (r-d+1),f (d+t))=∑ i ∈ range (n+1),f i := by
    have htrim : (∑ i ∈ range (r+1),f i)=∑ i ∈ range (n+1),f i := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      apply hz
      have hi' : ¬i < r+1 := by simpa only [mem_range] using hi
      right
      omega
    have hlow : (∑ i ∈ range d,f i)=0 := by
      apply sum_eq_zero
      intro i hi
      exact hz i (Or.inl (mem_range.mp hi))
    rw [show r+1=d+(r-d+1) by omega,sum_range_add,hlow,zero_add] at htrim
    exact htrim
  have sixJ_cycle_columns (a b c d e f : ℕ) :
      sixJ a b c d e f = sixJ c a b f d e := by
    have triangle_cycle (a b c : ℕ) : triangle a b c ↔ triangle c a b := by
      unfold triangle
      omega
    have deltaSq_cycle (a b c : ℕ) : deltaSq a b c = deltaSq c a b := by
      unfold deltaSq
      rw [show c+a-b=a+c-b by omega, show c+b-a=b+c-a by omega,
        show a+b-c=a+b-c by rfl, show c+a+b=a+b+c by omega]
      ring
    have ha : admissible a b c d e f ↔ admissible c a b f d e := by
      unfold admissible
      rw [← triangle_cycle a b c, ← triangle_cycle d e c,
        ← triangle_cycle a e f, ← triangle_cycle d b f]
      tauto
    have hlo : lower a b c d e f = lower c a b f d e := by
      unfold lower
      rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
        show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
      ac_rfl
    have hup : upper a b c d e f = upper c a b f d e := by
      unfold upper
      rw [show c+a+f+d=c+a+f+d by rfl, show a+b+d+e=a+b+d+e by rfl,
        show b+c+e+f=b+c+e+f by rfl]
      ac_rfl
    have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm c a b f d e z := by
      unfold racahTerm
      rw [show c+a+b=a+b+c by omega, show c+d+e=d+e+c by omega,
        show f+a+e=a+e+f by omega, show f+d+b=d+b+f by omega]
      congr 1
      ring
    have hr : racahSum a b c d e f = racahSum c a b f d e := by
      simp only [racahSum, ← hlo, ← hup, ← ht]
    have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
        deltaSq c a b*deltaSq c d e*deltaSq f a e*deltaSq f d b := by
      rw [← deltaSq_cycle a b c, ← deltaSq_cycle d e c,
        ← deltaSq_cycle a e f, ← deltaSq_cycle d b f]
      ring
    simp only [sixJ, ← ha, ← hd, ← hr]
  have W_swap (N i j l : ℕ) : W N i j l=W N i l j := by
    have sixJ_swap_columns (a b c d e f : ℕ) :
        sixJ a b c d e f = sixJ b a c e d f := by
      have deltaSq_swap (a b c : ℕ) : deltaSq a b c = deltaSq b a c := by
        unfold deltaSq
        rw [show b+a-c=a+b-c by omega, show b+a+c=a+b+c by omega]
        ring
      have triangle_swap (a b c : ℕ) : triangle a b c ↔ triangle b a c := by
        unfold triangle
        omega
      have ha : admissible a b c d e f ↔ admissible b a c e d f := by
        unfold admissible
        rw [← triangle_swap b a c, ← triangle_swap b d f,
          ← triangle_swap e a f, ← triangle_swap e d c]
        tauto
      have hlo : lower a b c d e f = lower b a c e d f := by
        unfold lower
        rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
          show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega]
        ac_rfl
      have hup : upper a b c d e f = upper b a c e d f := by
        unfold upper
        rw [show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
          show c+b+f+e=b+c+e+f by omega]
        ac_rfl
      have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm b a c e d f z := by
        unfold racahTerm
        rw [show b+a+c=a+b+c by omega, show e+a+f=a+e+f by omega,
          show e+d+c=d+e+c by omega, show b+d+f=d+b+f by omega,
          show b+a+e+d=a+b+d+e by omega, show a+c+d+f=c+a+f+d by omega,
          show c+b+f+e=b+c+e+f by omega]
        congr 1
        ring
      have hr : racahSum a b c d e f = racahSum b a c e d f := by
        simp only [racahSum, ← hlo, ← hup, ← ht]
      have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
          deltaSq b a c*deltaSq b d f*deltaSq e a f*deltaSq e d c := by
        rw [← deltaSq_swap b a c, ← deltaSq_swap b d f,
          ← deltaSq_swap e a f, ← deltaSq_swap e d c]
        ring
      simp only [sixJ, ← ha, ← hd, ← hr]
    unfold W
    calc
      _ = sixJ (2*l) (2*i) (2*j) (N-1) (N-1) (N-1) := sixJ_cycle_columns _ _ _ _ _ _
      _ = _ := sixJ_swap_columns _ _ _ _ _ _
  have unsigned_moment_ordered (N j l : ℕ) (hN : 2≤N)
      (hj : 1≤j ∧ j<N) (hl : 1≤l ∧ l<N) (hjl : j≤l) :
      (∑ i ∈ range (N-1),casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) j l^2) =
        (((N : ℝ)^2-1)*(casimir j+casimir l)-2*casimir j*casimir l)/
          ((N : ℝ)*((N : ℝ)^2-1)) := by
    have jacobi_diagonal_at_s (s j l : ℚ) (hs : s ≠ 0) (hs1 : s+1 ≠ 0) :
        rawDiagonal s s j l s =
          spinCasimir j+spinCasimir l-spinCasimir j*spinCasimir l/(2*s*(s+1)) := by
      unfold rawDiagonal spinCasimir
      field_simp [hs, hs1]
      ring
    have central_unsigned_moment (n j l : ℕ) (hn : 1≤n)
        (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
        ((n+1 : ℕ) : ℝ)*(∑ i ∈ range n,casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
          W (n+1) (i+1) j l^2) =
            (rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l ((n : ℚ)/2) : ℝ) := by
      have central_symbol_is_W (N i j l : ℕ) :
          sixJ (N-1) (N-1) (2*i) (2*j) (2*l) (N-1) = W N i j l := by
        have sixJ_flip_pair (a b c d e f : ℕ) :
            sixJ a b c d e f = sixJ d e c a b f := by
          have ha : admissible a b c d e f ↔ admissible d e c a b f := by
            unfold admissible
            tauto
          have hlo : lower a b c d e f = lower d e c a b f := by
            unfold lower
            ac_rfl
          have hup : upper a b c d e f = upper d e c a b f := by
            unfold upper
            rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
              show c+d+f+a=c+a+f+d by omega]
          have ht (z : ℕ) : racahTerm a b c d e f z = racahTerm d e c a b f z := by
            unfold racahTerm
            rw [show d+e+a+b=a+b+d+e by omega, show e+c+b+f=b+c+e+f by omega,
              show c+d+f+a=c+a+f+d by omega]
            congr 1
            ring
          have hr : racahSum a b c d e f = racahSum d e c a b f := by
            simp only [racahSum, ← hlo, ← hup, ← ht]
          have hd : deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c =
              deltaSq d e c*deltaSq d b f*deltaSq a e f*deltaSq a b c := by ring
          simp only [sixJ, ← ha, ← hd, ← hr]
        unfold W
        calc
          _ = sixJ (2*j) (2*l) (2*i) (N-1) (N-1) (N-1) := sixJ_flip_pair (N-1) (N-1) (2*i) (2*j) (2*l) (N-1)
          _ = sixJ (2*i) (2*j) (2*l) (N-1) (N-1) (N-1) := sixJ_cycle_columns (2*j) (2*l) (2*i) (N-1) (N-1) (N-1)
      have channel_center_label (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n)
          (hjl : j ≤ l) :
          ∃ t ≤ channelWidth n j l, channelLabel n j l t = n := by
        have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
        refine ⟨(n-channelBase n j l)/2, ?_, ?_⟩
        · unfold channelWidth channelBase
          omega
        · unfold channelLabel channelBase
          omega
      have physicalTU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
          physicalT n j l*physicalU n j l=physicalU n j l*
            diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)) := by
        have channel_last (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) (hjl : j ≤ l) :
            channelLabel n j l (channelWidth n j l) = n+2*j := by
          unfold channelLabel channelBase channelWidth
          have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
          omega
        have channel_admissible (n j l t u : ℕ) (hj : j ≤ n)
            (hl : l ≤ n) (hjl : j ≤ l) (ht : t ≤ channelWidth n j l)
            (hu : u ≤ channelWidth n j l) :
            admissible n n (2*(l-j+u)) (2*j) (2*l) (channelLabel n j l t) := by
          have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
          unfold channelWidth at ht hu
          unfold channelLabel channelBase admissible triangle
          omega
        have normalizedSixJ_zero (a b u c d y : ℕ) (h : ¬admissible a b u c d y) :
            normalizedSixJ a b u c d y=0 := by
          simp only [normalizedSixJ,sixJ,if_neg h,mul_zero]
        have channel_below_missing (n j l u : ℕ) (hjl : j≤l)
            (hy : 2≤channelBase n j l) :
            normalizedSixJ n n u (2*j) (2*l) (channelBase n j l-2)=0 := by
          apply normalizedSixJ_zero
          intro ha
          by_cases hn : j+l≤n
          · have hb : channelBase n j l=n-2*j := by unfold channelBase; omega
            have h := ha.2.2.1.2.1
            rw [hb] at hy h
            omega
          · have hb : channelBase n j l=2*l-n := by unfold channelBase; omega
            have h := ha.2.1.2.1
            rw [hb] at hy h
            omega
        have channel_above_missing (n j l u : ℕ) :
            normalizedSixJ n n u (2*j) (2*l) (n+2*j+2)=0 := by
          apply normalizedSixJ_zero
          intro ha
          have h := ha.2.2.1.2.2.1
          omega
        have physicalU_finite (n j l : ℕ) :
            physicalU n j l=finiteSixJMatrix n n (2*j) (2*l) (channelBase n j l)
              (channelWidth n j l) (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val)) := by
          exact rfl
        have he : channelBase n j l+2*channelWidth n j l+2=n+2*j+2 := by
          have h := channel_last n j l hj hl hjl
          unfold channelLabel at h
          omega
        have h := finiteSixJ_action n n (2*j) (2*l) (channelBase n j l) (channelWidth n j l)
          (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val))
          (fun k i => channel_admissible n j l k.val i.val hj hl hjl
            (by omega) (by omega))
          (fun i hb => channel_below_missing n j l (2*(l-j+i.val)) hjl hb)
          (fun i => by rw [he]; exact channel_above_missing n j l (2*(l-j+i.val)))
        have hc : (fun i : Fin (channelWidth n j l+1) =>
            ((((2*(l-j+i.val) : ℕ) : ℚ)/2*(((2*(l-j+i.val) : ℕ) : ℚ)/2+1) : ℚ) : ℝ)) =
            fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val) := by
          funext i
          unfold casimir
          push_cast
          ring
        rw [hc,←physicalU_finite] at h
        exact h
      rcases channel_center_label n j l hj hl hjl with ⟨t,ht,hlabel⟩
      let k : Fin (channelWidth n j l+1) := ⟨t,by omega⟩
      have hk : channelLabel n j l k.val=n := hlabel
      have hb : channelBase n j l+2*k.val=n := hk
      let f : ℕ → ℝ := fun i => casimir i*(2*(i : ℝ)+1)*sixJ n n (2*i) (2*j) (2*l) n^2
      have hfzero (i : ℕ) (hi : i < l-j ∨ min n (j+l) < i) : f i=0 := by
        have hnot : ¬admissible n n (2*i) (2*j) (2*l) n := by
          intro ha
          have h1 := ha.1
          have h4 := ha.2.2.2
          unfold triangle at h1 h4
          omega
        simp only [f,sixJ,if_neg hnot,zero_pow (by omega : (2 : ℕ)≠0),mul_zero]
      have hfsum : (∑ i : Fin (channelWidth n j l+1),f (l-j+i.val))=
          ∑ i ∈ range (n+1),f i := by
        unfold channelWidth
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (l-j+i))]
        apply sum_shifted_support f n (min n (j+l)) (l-j) (by omega) (by omega)
        exact hfzero
      have hsquare (i : Fin (channelWidth n j l+1)) :
          physicalU n j l k i^2=((n+1 : ℕ) : ℝ)*(2*((l-j+i.val : ℕ) : ℝ)+1)*
            sixJ n n (2*(l-j+i.val)) (2*j) (2*l) n^2 := by
        unfold physicalU
        rw [hk,mul_pow,Real.sq_sqrt (by positivity)]
        push_cast
        ring
      have hT : physicalT n j l k k=(recurrenceDiagonalQ n n (2*j) (2*l) n : ℝ) := by
        have hbad : ¬k.val+1=k.val := by omega
        simp [physicalT,finiteSixJJacobi,jacobiMatrix,upperBand,hb,hbad]
      have hmatrix := congrArg (fun A => A*(physicalU n j l)ᵀ) (physicalTU n j l hj hl hjl)
      rw [Matrix.mul_assoc,physicalU_orthogonality n j l hj hl hjl,Matrix.mul_one] at hmatrix
      have hm := congrArg (fun A => A k k) hmatrix
      rw [hT,Matrix.mul_apply] at hm
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply] at hm
      have hterm (i : Fin (channelWidth n j l+1)) :
          (physicalU n j l k i*casimir (l-j+i.val))*physicalU n j l k i=
            ((n+1 : ℕ) : ℝ)*f (l-j+i.val) := by
        calc
          _ = casimir (l-j+i.val)*(physicalU n j l k i)^2 := by ring
          _ = _ := by rw [hsquare]; unfold f; ring
      simp_rw [hterm] at hm
      rw [←Finset.mul_sum,hfsum] at hm
      have hf0 : f 0=0 := by simp [f,casimir]
      rw [sum_range_succ',hf0,add_zero] at hm
      have hjq : (((2*j : ℕ) : ℚ)/2)=(j : ℚ) := by push_cast; ring
      have hlq : (((2*l : ℕ) : ℚ)/2)=(l : ℚ) := by push_cast; ring
      simp only [recurrenceDiagonalQ,if_neg (by omega : n≠0),hjq,hlq] at hm
      have hW (i : ℕ) : sixJ n n (2*i) (2*j) (2*l) n=W (n+1) i j l := by
        simpa only [Nat.add_sub_cancel_right] using central_symbol_is_W (n+1) i j l
      dsimp [f] at hm
      simp_rw [hW] at hm
      exact hm.symm
    let n := N-1
    have hn : 1≤n := by dsimp [n]; omega
    have hjn : j≤n := by dsimp [n]; omega
    have hln : l≤n := by dsimp [n]; omega
    have hdimN : n+1=N := by dsimp [n]; omega
    have h := central_unsigned_moment n j l hn hjn hln hjl
    rw [hdimN] at h
    have hs : (n : ℚ)/2 ≠ 0 := by
      have hnp : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
      exact ne_of_gt (by positivity)
    have hs1 : (n : ℚ)/2+1 ≠ 0 := by positivity
    rw [jacobi_diagonal_at_s ((n : ℚ)/2) j l hs hs1] at h
    unfold spinCasimir at h
    push_cast at h
    have hNR : (n : ℝ)+1=(N : ℝ) := by exact_mod_cast hdimN
    have hden : 2*((n : ℝ)/2)*((n : ℝ)/2+1)=((N : ℝ)^2-1)/2 := by
      rw [←hNR]
      ring
    rw [hden] at h
    have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N≠0)
    have hNR2 : (2 : ℝ)≤N := by exact_mod_cast hN
    have hdne : (N : ℝ)^2-1 ≠ 0 := by nlinarith
    apply (eq_div_iff (mul_ne_zero hne hdne)).mpr
    field_simp [hdne] at h
    dsimp [n] at h
    unfold casimir at h ⊢
    push_cast at h ⊢
    linear_combination h
  by_cases horder : j≤l
  · exact unsigned_moment_ordered N j l hN hj hl horder
  · have h := unsigned_moment_ordered N l j hN hl hj (by omega)
    have he : (∑ i ∈ range (N-1),casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) l j^2) =
        ∑ i ∈ range (N-1),casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) j l^2 := by
      apply sum_congr rfl
      intro i _
      rw [W_swap N (i+1) l j]
    rw [he] at h
    convert h using 1 <;> ring

def claim : Prop := ∀ N : ℕ, 2 ≤ N →
  (∀ j l : ℕ, 1 ≤ j ∧ j < N → 1 ≤ l ∧ l < N → j ≠ l →
    (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*W N (i+1) j l^2) =
      1/((N : ℝ)* |(j : ℝ)-l| *(j+l+1))) ∧
  (∀ j l : ℕ, 1 ≤ j ∧ j < N → 1 ≤ l ∧ l < N →
    (∑ i ∈ range (N-1), (-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
      W N (i+1) j l^2) = (-1 : ℝ)^(N+1)*(casimir j+casimir l)*Wij N l j) ∧
  (∀ j l : ℕ, 1 ≤ j ∧ j < N → 1 ≤ l ∧ l < N →
    (∑ i ∈ range (N-1), casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) j l^2) =
      (((N : ℝ)^2-1)*(casimir j+casimir l)-2*casimir j*casimir l)/
        ((N : ℝ)*((N : ℝ)^2-1))) ∧
  (∀ j : ℕ, 1 ≤ j ∧ j < N →
    (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*
      (1/(N : ℝ)+(-1 : ℝ)^(i+1+j+N)*Wij N (i+1) j)) = 2*(harmonic j : ℝ)/N)

theorem result : claim := by
  have harmonic_sum_rule (N j : ℕ) (hN : 2 ≤ N) (hj : j < N)
      (hexp : ∀ i : ℕ, i < N →
        (-1 : ℝ)^(N-1+i+j)*N*Wij N i j = (racahPolynomial N j i : ℝ)) :
      (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
        (1/(N : ℝ) + (-1 : ℝ)^(i+1+j+N)*Wij N (i+1) j)) =
        2*(harmonic j : ℝ)/N := by
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hb : ∀ i ∈ range (N-1),
        1/(N : ℝ) + (-1 : ℝ)^(i+1+j+N)*Wij N (i+1) j =
          (1-(racahPolynomial N j (i+1) : ℝ))/N := by
      intro i hi
      have hi' : i+1 < N := by have := mem_range.mp hi; omega
      have he := hexp (i+1) hi'
      rw [show i+1+j+N = (N-1+(i+1)+j)+1 by omega, pow_succ]
      calc
        _ = (1-((-1 : ℝ)^(N-1+(i+1)+j)*N*Wij N (i+1) j))/N := by
          field_simp [hn0]
          ring
        _ = (1-(racahPolynomial N j (i+1) : ℝ))/N := by rw [he]
    have he : (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
        (1/(N : ℝ) + (-1 : ℝ)^(i+1+j+N)*Wij N (i+1) j)) =
        (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
        (1-(racahPolynomial N j (i+1) : ℝ)))/N := by
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      rw [hb i hi]
      ring
    rw [he]
    congr 1
    have hp := congrArg (fun q : ℚ => (q : ℝ)) (polynomial_harmonic N j hN hj)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
      Rat.cast_natCast, Rat.cast_add, Rat.cast_ofNat, casimir] using hp
  intro N hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun j l hj hl hjl => inverse_moment_open N j l hN hj hl hjl
  · exact fun j l hj hl => alternating_moment_open N j l hN hj hl
  · exact fun j l hj hl => unsigned_moment_open N j l hN hj hl
  · intro j hj
    apply harmonic_sum_rule N j hN hj.2
    intro i hi
    exact racah_expansion_open N i j hN hi hj.2

end D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules
