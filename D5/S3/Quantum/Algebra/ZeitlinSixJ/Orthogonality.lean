/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
physicalU_orthogonality:
  proof_shape: content
  escape_witness: endpoint_normalization: forall n,p,d with d<=n,p, sum i in range(p+1), endpointWeight n p d i = 1. It gives the actual stretched-row Gram anchor, which is live in dual_intertwining_orthogonality.
jacobi_green_inverse:
  proof_shape: content
  escape_witness: Local greenColumn_lower_residual and greenColumn_upper_residual: the neighboring weighted Green-column entries equal -(a k-L k)*greenColumn k h and -(a k-R k)*greenColumn k h on their respective sides of h. These product constructions and the diagonal value give every entry of the inverse identity.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence

noncomputable def physicalT (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  finiteSixJJacobi n n (2*j) (2*l) (channelBase n j l) (channelWidth n j l)

noncomputable def physicalH (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  finiteSixJJacobi n (2*l) (2*j) n (2*(l-j)) (channelWidth n j l)

noncomputable def physicalCasimir (n j l : ℕ) (k : Fin (channelWidth n j l+1)) : ℝ :=
  (((channelLabel n j l k.val : ℚ)/2*((channelLabel n j l k.val : ℚ)/2+1) : ℚ) : ℝ)

lemma physicalU_orthogonality (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
    physicalU n j l*(physicalU n j l)ᵀ=1 := by
  have stretched_racah_sum (n j d i : ℕ) (hdn : d ≤ n) (hdi : d ≤ i)
      (hin : i ≤ n) (hip : i ≤ 2*j+d) :
      racahSum n n (2*i) (2*j) (2*(j+d)) (n+2*j) =
        (-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1) /
          (Nat.factorial (2*j+d-i)*Nat.factorial d*Nat.factorial (n-i)*
            Nat.factorial i*Nat.factorial (i-d)) := by
    have hl : lower n n (2*i) (2*j) (2*(j+d)) (n+2*j) = n+2*j+d := by
      unfold lower
      omega
    have hu : upper n n (2*i) (2*j) (2*(j+d)) (n+2*j) = n+2*j+d := by
      unfold upper
      omega
    unfold racahSum
    rw [hl,hu,sum_eq_single (n+2*j+d)]
    · rw [if_pos (by omega)]
      unfold racahTerm
      rw [show (n+n+2*i)/2=n+i by omega,
        show (n+2*(j+d)+(n+2*j))/2=n+2*j+d by omega,
        show (2*j+n+(n+2*j))/2=n+2*j by omega,
        show (2*j+2*(j+d)+2*i)/2=2*j+d+i by omega,
        show (n+n+2*j+2*(j+d))/2=n+2*j+d by omega,
        show (n+2*i+2*(j+d)+(n+2*j))/2=n+2*j+d+i by omega,
        show (2*i+n+(n+2*j)+2*j)/2=n+2*j+i by omega,
        show n+2*j+d-(n+i)=2*j+d-i by omega,
        show n+2*j+d-(n+2*j)=d by omega,
        show n+2*j+d-(2*j+d+i)=n-i by omega,
        show n+2*j+d+i-(n+2*j+d)=i by omega,
        show n+2*j+i-(n+2*j+d)=i-d by omega]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    · intro z hz hne
      rw [if_neg (by simp only [mem_range] at hz; omega)]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
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
  have physicalU_anchor (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      (physicalU n j l*(physicalU n j l)ᵀ)
        (Fin.last (channelWidth n j l)) (Fin.last (channelWidth n j l))=1 := by
    have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) :
        endpointKernel n p d i = 0 := by
      have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
        simp only [invFactorial, if_neg (not_le.mpr hz)]
      unfold endpointKernel
      rcases h with h | h | h
      · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
      · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
      · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
    have endpoint_shifted_normalization (n p d : ℕ) (hd : d≤n) (hp : d≤p) :
        (∑ t ∈ range (min n p-d+1), endpointWeight n p d (d+t)) = 1 := by
      have endpointWeight_zero (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) :
          endpointWeight n p d i = 0 := by
        rw [endpointWeight,endpointKernel_vanish n p d i h,mul_zero]
      have hfull := endpoint_normalization n p d hd hp
      have htrim : (∑ i ∈ range (min n p+1),endpointWeight n p d i) =
          ∑ i ∈ range (p+1),endpointWeight n p d i := by
        apply sum_subset (range_mono (by omega))
        intro i _ hi
        apply endpointWeight_zero
        have hi' : ¬i < min n p+1 := by simpa only [mem_range] using hi
        omega
      have hlow : (∑ i ∈ range d,endpointWeight n p d i)=0 := by
        apply sum_eq_zero
        intro i hi
        exact endpointWeight_zero n p d i (Or.inl (mem_range.mp hi))
      rw [show min n p+1=d+(min n p-d+1) by omega,sum_range_add,hlow,zero_add] at htrim
      exact htrim.trans hfull
    have physicalU_stretched_square (n j l : ℕ) (hj : j≤n) (hl : l≤n)
        (hjl : j≤l) (i : Fin (channelWidth n j l+1)) :
        (physicalU n j l (Fin.last (channelWidth n j l)) i)^2 =
          (endpointWeight n (j+l) (l-j) (l-j+i.val) : ℝ) := by
      have stretched_row_square (n j d i : ℕ) (hdn : d ≤ n) :
          ((n+2*j+1 : ℕ) : ℝ)*(2*(i : ℝ)+1)*
            sixJ n n (2*i) (2*j) (2*(j+d)) (n+2*j)^2 =
              (endpointWeight n (2*j+d) d i : ℝ) := by
        have endpointWeight_factorials (n p d i : ℕ)
            (hd : d ≤ n) (hp : d ≤ p) (hdi : d ≤ i) (hin : i ≤ n) (hip : i ≤ p) :
            endpointWeight n p d i =
              ((Nat.factorial (n-d)*Nat.factorial p*Nat.factorial (p-d)*Nat.factorial n*
                Nat.factorial (n+p+1) : ℚ)/(Nat.factorial d*Nat.factorial (n+p-d))) *
                ((2*(i : ℚ)+1)*Nat.factorial (i+d)/
                  (Nat.factorial (n-i)*Nat.factorial (p-i)*Nat.factorial (i-d)*
                    Nat.factorial (n+i+1)*Nat.factorial (p+i+1))) := by
          have invFactorial_nat (n : ℕ) :
              invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
            simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
          have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) :
              invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
            rw [← Int.natCast_sub h, invFactorial_nat]
          unfold endpointWeight endpointConstant endpointKernel
          rw [invFactorial_nat_sub n i hin, invFactorial_nat_sub p i hip,
            invFactorial_nat_sub i d hdi,
            show (n : ℤ)+i+1 = ((n+i+1 : ℕ) : ℤ) by omega,
            show (p : ℤ)+i+1 = ((p+i+1 : ℕ) : ℤ) by omega,
            show (n : ℤ)+p-d = ((n+p : ℕ) : ℤ)-(d : ℤ) by omega,
            invFactorial_nat_sub (n+p) d (by omega), invFactorial_nat, invFactorial_nat,
            invFactorial_nat]
          simp only [div_eq_mul_inv, _root_.mul_inv_rev]
          ring
        have sixJ_square (a b c d e f : ℕ) (ha : admissible a b c d e f) :
            sixJ a b c d e f ^ 2 =
              ((deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c*
                racahSum a b c d e f ^ 2 : ℚ) : ℝ) := by
          have deltaSq_pos (a b c : ℕ) : 0 < deltaSq a b c := by
            unfold deltaSq
            positivity
          have hq : (0 : ℚ) ≤ deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c := by
            have h1 := deltaSq_pos a b c
            have h2 := deltaSq_pos a e f
            have h3 := deltaSq_pos d b f
            have h4 := deltaSq_pos d e c
            positivity
          have hr : (0 : ℝ) ≤ ((deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c : ℚ) : ℝ) := by
            exact_mod_cast hq
          rw [sixJ, if_pos ha, mul_pow, Real.sq_sqrt hr]
          push_cast
          rfl
        have stretched_delta_first (n i : ℕ) (hi : i ≤ n) :
            deltaSq n n (2*i) =
              Nat.factorial (n-i)*Nat.factorial i*Nat.factorial i / (Nat.factorial (n+i+1) : ℚ) := by
          unfold deltaSq
          rw [show (n+n-2*i)/2=n-i by omega,
            show (n+2*i-n)/2=i by omega,
            show (n+n+2*i)/2+1=n+i+1 by omega]
        have stretched_delta_second (n j d : ℕ) (hd : d ≤ n) :
            deltaSq n (2*(j+d)) (n+2*j) =
              Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d) /
                (Nat.factorial (n+2*j+d+1) : ℚ) := by
          unfold deltaSq
          rw [show (n+2*(j+d)-(n+2*j))/2=d by omega,
            show (n+(n+2*j)-2*(j+d))/2=n-d by omega,
            show (2*(j+d)+(n+2*j)-n)/2=2*j+d by omega,
            show (n+2*(j+d)+(n+2*j))/2+1=n+2*j+d+1 by omega]
        have stretched_delta_third (n j : ℕ) :
            deltaSq (2*j) n (n+2*j) =
              Nat.factorial (2*j)*Nat.factorial n / (Nat.factorial (n+2*j+1) : ℚ) := by
          unfold deltaSq
          rw [show (2*j+n-(n+2*j))/2=0 by omega,
            show (2*j+(n+2*j)-n)/2=2*j by omega,
            show (n+(n+2*j)-2*j)/2=n by omega,
            show (2*j+n+(n+2*j))/2+1=n+2*j+1 by omega]
          simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
        have stretched_delta_fourth (j d i : ℕ) (hd : d ≤ i) (hi : i ≤ 2*j+d) :
            deltaSq (2*j) (2*(j+d)) (2*i) =
              Nat.factorial (2*j+d-i)*Nat.factorial (i-d)*Nat.factorial (i+d) /
                (Nat.factorial (2*j+d+i+1) : ℚ) := by
          unfold deltaSq
          rw [show (2*j+2*(j+d)-2*i)/2=2*j+d-i by omega,
            show (2*j+2*i-2*(j+d))/2=i-d by omega,
            show (2*(j+d)+2*i-2*j)/2=i+d by omega,
            show (2*j+2*(j+d)+2*i)/2+1=2*j+d+i+1 by omega]
        by_cases hdi : d ≤ i
        · by_cases hin : i ≤ n
          · by_cases hip : i ≤ 2*j+d
            · have ha : admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
                unfold admissible triangle
                omega
              rw [sixJ_square _ _ _ _ _ _ ha]
              rw [stretched_delta_first n i hin, stretched_delta_second n j d hdn,
                stretched_delta_third n j, stretched_delta_fourth j d i hdi hip,
                stretched_racah_sum n j d i hdn hdi hin hip,
                endpointWeight_factorials n (2*j+d) d i hdn (by omega) hdi hin hip]
              have hsign : ((-1 : ℚ)^(n+2*j+d))^2 = 1 := by
                rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
              have he : ((n+2*j+1 : ℕ) : ℚ)*(2*(i : ℚ)+1)*
                ((Nat.factorial (n-i)*Nat.factorial i*Nat.factorial i/(Nat.factorial (n+i+1) : ℚ))*
                  (Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d)/(Nat.factorial (n+2*j+d+1) : ℚ))*
                  (Nat.factorial (2*j)*Nat.factorial n/(Nat.factorial (n+2*j+1) : ℚ))*
                  (Nat.factorial (2*j+d-i)*Nat.factorial (i-d)*Nat.factorial (i+d)/(Nat.factorial (2*j+d+i+1) : ℚ))*
                  ((-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1)/
                    (Nat.factorial (2*j+d-i)*Nat.factorial d*Nat.factorial (n-i)*Nat.factorial i*Nat.factorial (i-d)))^2) =
                (Nat.factorial (n-d)*Nat.factorial (2*j+d)*Nat.factorial (2*j+d-d)*Nat.factorial n*
                    Nat.factorial (n+(2*j+d)+1)/(Nat.factorial d*Nat.factorial (n+(2*j+d)-d) : ℚ))*
                  ((2*(i : ℚ)+1)*Nat.factorial (i+d)/(Nat.factorial (n-i)*Nat.factorial (2*j+d-i)*
                    Nat.factorial (i-d)*Nat.factorial (n+i+1)*Nat.factorial (2*j+d+i+1) : ℚ)) := by
                rw [div_pow, mul_pow, hsign, one_mul,
                  show 2*j+d-d=2*j by omega, show n+(2*j+d)-d=n+2*j by omega,
                  show n+(2*j+d)+1=n+2*j+d+1 by omega, Nat.factorial_succ (n+2*j)]
                have hf : ∀ t : ℕ, (Nat.factorial t : ℚ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
                have hn : ((n+2*j+1 : ℕ) : ℚ) ≠ 0 := by positivity
                field_simp
                push_cast
                ring
              exact_mod_cast he
            · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
                unfold admissible triangle
                omega
              rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inr (Or.inr (by omega)))]
              simp
          · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
              unfold admissible triangle
              omega
            rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inr (Or.inl (by omega)))]
            simp
        · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
            unfold admissible triangle
            omega
          rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inl (by omega))]
          simp
      have hdn : l-j≤n := by omega
      have hlast := channel_last n j l hj hl hjl
      have h := stretched_row_square n j (l-j) (l-j+i.val) hdn
      have hl' : j+(l-j)=l := by omega
      have hp : 2*j+(l-j)=j+l := by omega
      rw [hl',hp] at h
      unfold physicalU
      simp only [Fin.val_last,hlast,mul_pow]
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      convert h using 1 <;> push_cast <;> ring
    simp only [Matrix.mul_apply,Matrix.transpose_apply,←sq]
    simp_rw [physicalU_stretched_square n j l hj hl hjl]
    have hn := endpoint_shifted_normalization n (j+l) (l-j) (by omega) (by omega)
    unfold channelWidth
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
      (endpointWeight n (j+l) (l-j) (l-j+t) : ℝ))]
    exact_mod_cast hn
  have normalizedSixJ_zero (a b u c d y : ℕ) (h : ¬admissible a b u c d y) :
      normalizedSixJ a b u c d y=0 := by
    simp only [normalizedSixJ,sixJ,if_neg h,mul_zero]
  have finiteSixJJacobi_symmetric (a b c d base m : ℕ) :
      (finiteSixJJacobi a b c d base m)ᵀ=finiteSixJJacobi a b c d base m := by
    have jacobiMatrix_symmetric (m : ℕ) (a e : Fin (m+1) → ℝ) :
        (jacobiMatrix m a e)ᵀ=jacobiMatrix m a e := by
      simp only [jacobiMatrix,Matrix.transpose_add,Matrix.diagonal_transpose,Matrix.transpose_transpose]
      abel
    exact jacobiMatrix_symmetric m _ _
  have physicalTU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      physicalT n j l*physicalU n j l=physicalU n j l*
        diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)) := by
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
  have physicalDU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      diagonal (physicalCasimir n j l)*physicalU n j l=physicalU n j l*physicalH n j l := by
    have admissible_flip_last (a b u c d y : ℕ) :
        admissible a b u c d y ↔ admissible a d y c b u := by
      unfold admissible
      tauto
    have physicalU_dual (n j l : ℕ) :
        (physicalU n j l)ᵀ=finiteSixJMatrix n (2*l) (2*j) n (2*(l-j))
          (channelWidth n j l) (fun k : Fin (channelWidth n j l+1) => channelLabel n j l k.val) := by
      have normalizedSixJ_dual (a b u c d y : ℕ) :
          normalizedSixJ a b u c d y=normalizedSixJ a d y c b u := by
        have sixJ_flip_last (a b u c d y : ℕ) :
            sixJ a b u c d y=sixJ a d y c b u := by
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
          calc
            _ = sixJ u a b y c d := sixJ_cycle_columns a b u c d y
            _ = sixJ b u a d y c := sixJ_cycle_columns u a b y c d
            _ = sixJ d y a b u c := sixJ_flip_pair b u a d y c
            _ = sixJ a d y c b u := sixJ_cycle_columns d y a b u c
        unfold normalizedSixJ
        rw [sixJ_flip_last]
        congr 1
        congr 1
        ring
      ext i k
      change normalizedSixJ n n (2*(l-j+i.val)) (2*j) (2*l) (channelLabel n j l k.val) =
        normalizedSixJ n (2*l) (channelLabel n j l k.val) (2*j) n (2*(l-j)+2*i.val)
      have he : 2*(l-j+i.val)=2*(l-j)+2*i.val := by omega
      simpa only [he] using normalizedSixJ_dual n n (2*(l-j+i.val)) (2*j) (2*l) (channelLabel n j l k.val)
    have h := finiteSixJ_action n (2*l) (2*j) n (2*(l-j)) (channelWidth n j l)
      (fun k : Fin (channelWidth n j l+1) => channelLabel n j l k.val)
      (fun i k => by
        have ha := channel_admissible n j l k.val i.val hj hl hjl (by omega) (by omega)
        have he : 2*(l-j+i.val)=2*(l-j)+2*i.val := by omega
        rw [he] at ha
        exact (admissible_flip_last _ _ _ _ _ _).mp ha)
      (fun k hb => by
        apply normalizedSixJ_zero
        intro ha
        have hbad := ha.2.2.1.2.1
        omega)
      (fun k => by
        apply normalizedSixJ_zero
        intro ha
        have hn := ha.2.1.2.2.1
        have hp := ha.2.2.1.2.2.1
        unfold channelWidth at hn hp
        omega)
    rw [←physicalU_dual] at h
    have ht := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.diagonal_transpose,
      finiteSixJJacobi_symmetric] at ht
    exact ht.symm
  have physicalCasimir_injective (n j l : ℕ) : Function.Injective (physicalCasimir n j l) := by
    have channel_spin_injective (n j l : ℕ) :
        Function.Injective (fun t : ℕ => ((channelLabel n j l t : ℚ)/2)*
          ((channelLabel n j l t : ℚ)/2+1)) := by
      have channel_spin_nonnegative (n j l t : ℕ) :
          (0 : ℚ) ≤ (channelLabel n j l t : ℚ)/2 := by
       positivity
      intro t u he
      have hxt := channel_spin_nonnegative n j l t
      have hxu := channel_spin_nonnegative n j l u
      have hsum : (channelLabel n j l t : ℚ)/2+(channelLabel n j l u : ℚ)/2+1 ≠ 0 := by
        linarith
      have hprod : ((channelLabel n j l t : ℚ)/2-(channelLabel n j l u : ℚ)/2)*
          ((channelLabel n j l t : ℚ)/2+(channelLabel n j l u : ℚ)/2+1) = 0 := by
        nlinarith [he]
      have hx := (mul_eq_zero.mp hprod).resolve_right hsum
      have hlab : channelLabel n j l t = channelLabel n j l u := by
        have hq : (channelLabel n j l t : ℚ) = (channelLabel n j l u : ℚ) := by linarith
        exact_mod_cast hq
      unfold channelLabel at hlab
      omega
    intro k h he
    apply Fin.ext
    apply channel_spin_injective n j l
    unfold physicalCasimir at he
    exact_mod_cast he
  have physicalT_edge_positive (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l)
      (t : Fin (channelWidth n j l)) : 0 < physicalT n j l t.castSucc t.succ := by
    have recurrence_upper_positive (a b u c d y : ℕ)
        (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) :
        0 < recurrenceUpperCoefficient a b c d y := by
      have raising_factors_positive (a b u c d y : ℕ)
          (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) :
          0 < raisingNumerator a b c d y ∧ 0 < raisingDenominator a b c d y := by
        have deltaSq_raise_factors_positive (a b c : ℕ) (ht : triangle a b c)
            (hi : c+2 ≤ a+b) :
            (0 : ℚ) < ((c : ℚ)/2+1)^2-(((a : ℚ)-b)/2)^2 ∧
              (0 : ℚ) < (((a : ℚ)+b)/2+1)^2-((c : ℚ)/2+1)^2 := by
          have triangle_difference_halves (a b c : ℕ) (ht : triangle a b c) :
              ((((a+b-c)/2 : ℕ) : ℚ) = ((a : ℚ)+b-c)/2) ∧
              ((((a+c-b)/2 : ℕ) : ℚ) = ((a : ℚ)+c-b)/2) ∧
              ((((b+c-a)/2 : ℕ) : ℚ) = ((b : ℚ)+c-a)/2) ∧
              ((((a+b+c)/2 : ℕ) : ℚ) = ((a : ℚ)+b+c)/2) := by
            have half_cast (n : ℕ) (hn : n % 2 = 0) :
                (((n/2 : ℕ) : ℤ) : ℚ) = (n : ℚ)/2 := by
              have he : 2*(n/2) = n := by omega
              have hq := congrArg (fun k : ℕ => (k : ℚ)) he
              simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
              simp only [Int.cast_natCast]
              apply (eq_div_iff (by positivity : (2 : ℚ) ≠ 0)).mpr
              simpa only [mul_comm] using hq
            rcases ht with ⟨ha,hb,hc,hp⟩
            have hp1 : (a+b-c)%2=0 := by omega
            have hp2 : (a+c-b)%2=0 := by omega
            have hp3 : (b+c-a)%2=0 := by omega
            have h1 := half_cast (a+b-c) hp1
            have h2 := half_cast (a+c-b) hp2
            have h3 := half_cast (b+c-a) hp3
            have h4 := half_cast (a+b+c) hp
            simp only [Int.cast_natCast,Nat.cast_sub hc,Nat.cast_sub hb,Nat.cast_sub ha,Nat.cast_add] at *
            exact ⟨h1,h2,h3,h4⟩
          rcases triangle_difference_halves a b c ht with ⟨h1,h2,h3,h4⟩
          have h1p : (0 : ℚ) < (((a+b-c)/2 : ℕ) : ℚ) := by
            exact_mod_cast (by omega : 0 < (a+b-c)/2)
          have h2p : (0 : ℚ) < (((a+c-b)/2 : ℕ) : ℚ)+1 := by positivity
          have h3p : (0 : ℚ) < (((b+c-a)/2 : ℕ) : ℚ)+1 := by positivity
          have h4p : (0 : ℚ) < (((a+b+c)/2 : ℕ) : ℚ)+2 := by positivity
          rw [h1] at h1p
          rw [h2] at h2p
          rw [h3] at h3p
          rw [h4] at h4p
          constructor
          · have h := mul_pos h2p h3p
            convert h using 1 <;> first | rfl | ring
          · have h := mul_pos h1p h4p
            convert h using 1 <;> first | rfl | ring
        have ha := deltaSq_raise_factors_positive a d y had.2.1 hp.2.1.2.2.1
        have hb := deltaSq_raise_factors_positive c b y had.2.2.1 hp.2.2.1.2.2.1
        constructor
        · unfold raisingNumerator
          have h := mul_pos ha.1 hb.1
          convert h using 1 <;> first | rfl | ring
        · unfold raisingDenominator
          have h := mul_pos ha.2 hb.2
          convert h using 1 <;> first | rfl | ring
      have hpos := raising_factors_positive a b u c d y had hp
      unfold recurrenceUpperCoefficient
      apply div_pos
      · apply Real.sqrt_pos.mpr
        exact_mod_cast mul_pos hpos.1 hpos.2
      · push_cast
        positivity
    have finiteSixJJacobi_edge (a b c d base m : ℕ) (t : Fin m) :
        finiteSixJJacobi a b c d base m t.castSucc t.succ=normalizedUpper a b c d (base+2*t.val) := by
      have he : t.castSucc ≠ t.succ := by intro h; have hv := congrArg Fin.val h; simp at hv
      have hbad : ¬t.val+1+1=t.val := by omega
      simp [finiteSixJJacobi,jacobiMatrix,upperBand,Matrix.diagonal,he,hbad]
    rw [physicalT,finiteSixJJacobi_edge]
    unfold normalizedUpper
    apply div_pos
    · apply mul_pos
      · refine recurrence_upper_positive n n (2*(l-j)) (2*j) (2*l) (channelBase n j l+2*t.val) ?_ ?_
        · exact channel_admissible n j l t.val 0 hj hl hjl (by omega) (by omega)
        · have ha := channel_admissible n j l (t.val+1) 0 hj hl hjl (by omega) (by omega)
          have he : channelLabel n j l (t.val+1)=channelBase n j l+2*t.val+2 := by unfold channelLabel; omega
          simpa only [he,Nat.add_zero] using ha
      · positivity
    · positivity
  apply dual_intertwining_orthogonality (channelWidth n j l) (physicalU n j l)
    (physicalT n j l) (physicalH n j l) (physicalCasimir n j l)
    (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val))
  · exact physicalCasimir_injective n j l
  · exact finiteSixJJacobi_symmetric _ _ _ _ _ _
  · exact finiteSixJJacobi_symmetric _ _ _ _ _ _
  · exact physicalTU n j l hj hl hjl
  · exact physicalDU n j l hj hl hjl
  · intro t
    exact ne_of_gt (physicalT_edge_positive n j l hj hl hjl t)
  · exact physicalU_anchor n j l hj hl hjl

noncomputable def greenColumn (a e L R : ℕ → ℝ) (k h : ℕ) : ℝ :=
  (L h+R h-a h)⁻¹ *
    if k≤h then ∏ t ∈ Ico k h, -e t/L t
    else ∏ t ∈ Ico h k, -e t/R (t+1)

noncomputable def greenMatrix (m : ℕ) (a e L R : ℕ → ℝ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun k h => greenColumn a e L R k.val h.val

lemma jacobi_green_inverse (m : ℕ) (a e L R : ℕ → ℝ)
    (hL : ∀ k≤m,L k≠0) (hR : ∀ k≤m,R k≠0)
    (hg : ∀ k≤m,L k+R k-a k≠0) (h0 : a 0=L 0) (hm : a m=R m)
    (hlower : ∀ k, 0<k → k≤m → e (k-1)^2=L (k-1)*(a k-L k))
    (hupper : ∀ k, k<m → e k^2=R (k+1)*(a k-R k)) :
    jacobiMatrix m (fun k => a k.val) (fun k => e k.val)*greenMatrix m a e L R=1 := by
  have upperBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      (upperBand m e*U) i h =
        if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,upperBand]
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val+1,by omega⟩ : Fin (m+1))]
      · simp
      · intro j _ hj
        have hn : i.val+1 ≠ j.val := by
          intro he
          apply hj
          apply Fin.ext
          exact he.symm
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : i.val+1 ≠ j.val := by omega
      simp only [if_neg hn,zero_mul]
  have lowerBand_mul (m : ℕ) (e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      ((upperBand m e)ᵀ*U) i h =
        if hi : 0 < i.val then
          e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0 := by
    classical
    simp only [Matrix.mul_apply,Matrix.transpose_apply,upperBand]
    by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single (⟨i.val-1,by omega⟩ : Fin (m+1))]
      · have he : i.val-1+1=i.val := by omega
        simp only [Fin.val_mk,if_pos he]
      · intro j _ hj
        have hn : j.val+1 ≠ i.val := by
          intro he
          apply hj
          apply Fin.ext
          change j.val=i.val-1
          omega
        simp only [if_neg hn,zero_mul]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hn : j.val+1 ≠ i.val := by omega
      simp only [if_neg hn,zero_mul]
  have jacobiMatrix_mul (m : ℕ) (a e : Fin (m+1) → ℝ)
      (U : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i : Fin (m+1)) (h : Fin (m+1)) :
      (jacobiMatrix m a e*U) i h = a i*U i h +
        (if hi : i.val < m then e i*U ⟨i.val+1,by omega⟩ h else 0) +
        (if hi : 0 < i.val then e ⟨i.val-1,by omega⟩*U ⟨i.val-1,by omega⟩ h else 0) := by
    simp only [jacobiMatrix,Matrix.add_mul,Matrix.add_apply,Matrix.diagonal_mul,
      upperBand_mul,lowerBand_mul]
  have greenColumn_diag (a e L R : ℕ → ℝ) (h : ℕ) :
      greenColumn a e L R h h=(L h+R h-a h)⁻¹ := by
    simp [greenColumn]
  have greenColumn_left (a e L R : ℕ → ℝ) (k h : ℕ) (hkh : k<h)
      (hL : L k≠0) :
      L k*greenColumn a e L R k h+e k*greenColumn a e L R (k+1) h=0 := by
    simp only [greenColumn,if_pos hkh.le,if_pos (by omega : k+1≤h)]
    rw [prod_eq_prod_Ico_succ_bot hkh]
    field_simp
    ring
  have greenColumn_right (a e L R : ℕ → ℝ) (k h : ℕ) (hkh : h<k)
      (hR : R k≠0) :
      R k*greenColumn a e L R k h+e (k-1)*greenColumn a e L R (k-1) h=0 := by
    have he : k-1+1=k := by omega
    have hp : h≤k-1 := by omega
    have hs : greenColumn a e L R (k-1) h =
        (L h+R h-a h)⁻¹*(∏ t ∈ Ico h (k-1),-e t/R (t+1)) := by
      by_cases hh : k-1=h
      · subst h
        simp [greenColumn]
      · simp only [greenColumn,if_neg (by omega : ¬k-1≤h)]
    rw [hs]
    simp only [greenColumn,if_neg (by omega : ¬k≤h)]
    rw [←he,prod_Ico_succ_top hp]
    rw [he]
    field_simp
    ring
  have greenColumn_lower_residual (m : ℕ) (a e L R : ℕ → ℝ)
      (hL : ∀ k≤m,L k≠0) (h0 : a 0=L 0)
      (hedge : ∀ k, 0<k → k≤m → e (k-1)^2=L (k-1)*(a k-L k))
      (k h : ℕ) (hk : k≤m) (hkh : k≤h) :
      (if 0<k then e (k-1)*greenColumn a e L R (k-1) h else 0) =
        -(a k-L k)*greenColumn a e L R k h := by
    by_cases hp : 0<k
    · rw [if_pos hp]
      have hb := greenColumn_left a e L R (k-1) h (by omega) (hL (k-1) (by omega))
      rw [show k-1+1=k by omega] at hb
      have he := hedge k hp hk
      apply mul_left_cancel₀ (hL (k-1) (by omega))
      linear_combination e (k-1)*hb - greenColumn a e L R k h*he
    · have hz : k=0 := by omega
      subst k
      simp [h0]
  have greenColumn_upper_residual (m : ℕ) (a e L R : ℕ → ℝ)
      (hR : ∀ k≤m,R k≠0) (hm : a m=R m)
      (hedge : ∀ k, k<m → e k^2=R (k+1)*(a k-R k))
      (k h : ℕ) (hk : k≤m) (hkh : h≤k) :
      (if k<m then e k*greenColumn a e L R (k+1) h else 0) =
        -(a k-R k)*greenColumn a e L R k h := by
    by_cases hp : k<m
    · rw [if_pos hp]
      have hb := greenColumn_right a e L R (k+1) h (by omega) (hR (k+1) (by omega))
      simp only [Nat.add_sub_cancel_right] at hb
      have he := hedge k hp
      apply mul_left_cancel₀ (hR (k+1) (by omega))
      linear_combination e k*hb - greenColumn a e L R k h*he
    · have hz : k=m := by omega
      subst k
      simp [hm]
  classical
  ext k h
  rw [jacobiMatrix_mul]
  simp only [greenMatrix,Fin.val_mk]
  have hk : k.val≤m := by omega
  have hh : h.val≤m := by omega
  rcases lt_trichotomy k.val h.val with hlt|heq|hgt
  · have he : k≠h := by intro he; have hv := congrArg Fin.val he; omega
    simp only [Matrix.one_apply,if_neg he, dif_pos (by omega : k.val<m)]
    have hb := greenColumn_left a e L R k.val h.val hlt (hL k.val hk)
    have hlo := greenColumn_lower_residual m a e L R hL h0 hlower k.val h.val hk hlt.le
    rw [show (if hp : 0<k.val then e (k.val-1)*greenColumn a e L R (k.val-1) h.val else 0)=
      (if 0<k.val then e (k.val-1)*greenColumn a e L R (k.val-1) h.val else 0) by rfl, hlo]
    linear_combination hb
  · have he : k=h := Fin.ext heq
    subst h
    simp only [Matrix.one_apply,if_pos rfl]
    have hlo := greenColumn_lower_residual m a e L R hL h0 hlower k.val k.val hk le_rfl
    have hup := greenColumn_upper_residual m a e L R hR hm hupper k.val k.val hk le_rfl
    rw [show (if hp : 0<k.val then e (k.val-1)*greenColumn a e L R (k.val-1) k.val else 0)=
      (if 0<k.val then e (k.val-1)*greenColumn a e L R (k.val-1) k.val else 0) by rfl,
      show (if hp : k.val<m then e k.val*greenColumn a e L R (k.val+1) k.val else 0)=
      (if k.val<m then e k.val*greenColumn a e L R (k.val+1) k.val else 0) by rfl,hlo,hup,
      greenColumn_diag]
    calc
      _ = (L k.val+R k.val-a k.val)*(L k.val+R k.val-a k.val)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ (hg k.val hk)
  · have he : k≠h := by intro he; have hv := congrArg Fin.val he; omega
    simp only [Matrix.one_apply,if_neg he,dif_pos (by omega : 0<k.val)]
    have hb := greenColumn_right a e L R k.val h.val hgt (hR k.val hk)
    have hup := greenColumn_upper_residual m a e L R hR hm hupper k.val h.val hk hgt.le
    rw [show (if hp : k.val<m then e k.val*greenColumn a e L R (k.val+1) h.val else 0)=
      (if k.val<m then e k.val*greenColumn a e L R (k.val+1) h.val else 0) by rfl,hup]
    linear_combination hb

def channelSpin (n j l t : ℕ) : ℚ := (channelLabel n j l t : ℚ)/2

noncomputable def physicalA (n j l t : ℕ) : ℝ :=
  (recurrenceDiagonalQ n n (2*j) (2*l) (channelLabel n j l t) : ℝ)

noncomputable def physicalE (n j l t : ℕ) : ℝ :=
  normalizedUpper n n (2*j) (2*l) (channelLabel n j l t)

noncomputable def physicalLP (n j l t : ℕ) : ℝ :=
  (pivotLeft ((n : ℚ)/2) j l (channelSpin n j l t) : ℝ)

noncomputable def physicalRP (n j l t : ℕ) : ℝ :=
  (pivotRight ((n : ℚ)/2) j l (channelSpin n j l t) : ℝ)

noncomputable def physicalG (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  greenMatrix (channelWidth n j l) (physicalA n j l) (physicalE n j l)
    (physicalLP n j l) (physicalRP n j l)

noncomputable def physicalSpectralInverse (n j l : ℕ) :
    Matrix (Fin (channelWidth n j l+1)) (Fin (channelWidth n j l+1)) ℝ :=
  physicalU n j l*diagonal (fun i : Fin (channelWidth n j l+1) => (casimir (l-j+i.val))⁻¹)*
    (physicalU n j l)ᵀ

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
