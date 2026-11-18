# The literal prime-cube six-return count

## Abstract

The original alternating six-return count in a prime-cube area range, with every scalar involution center and every prime retained.

**Theorem 1.1 (Every fixed area exponent below twenty-six sevenths).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count_of_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count_of_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, C0>=1 and fixed real alpha<26/7 there is one K>0, independent of the prime, the widths and the alternating units, such that the total literal six-letter count is at most K*Y^2*p^epsilon whenever p^(3/2)<=X<=Y, XY<=C0*p^alpha and 6Y<p^2. The count sums over every gamma modulo p^3 with gamma squared equal to one. There is no supplied chart, lattice estimate or count; all integer rows, ordered multiplicities, zero and nonunit branches and small primes are retained.

The structural actual degree-two resultant has seventh weighted height. A quadratic factor of a genuine cubic gains an extra J/I, and its mixed resultant has sixth weighted height; the cubic residual still has seventh weighted height. PascadiSeventhHeightCover combines all of these branches. The actual coordinate product is at most 32XY/p^3, so a fixed seventh-height constant times its seventh power is below p^5 for every sufficiently large prime precisely when alpha<26/7. The enlarged number-field value envelope uses T=p^2 and epsilon/2, keeping one field-uniform p^epsilon constant without the old cubic-height cutoff. The zero-reduction branches require only the small-height consequences already forced by this seventh-height gap.

The actual bad-degree average, retained-record count and six-branch unit-middle assembly consume these bounds. The moment error is absorbed for every alpha<=15/4, which includes alpha<26/7. Apply the all-center comparison at 2X,2Y with area constant 4C0, restore nonunit rows under 3*(2Y)<p^2, and sum over at most four scalar centers. Below the positive threshold P supplied by seventh_area_height_cutoff, the literal bound 729Y^6 and Y<=P^2 give a uniform multiple of Y^2*p^epsilon. Neither alpha=26/7 nor unrestricted moduli are asserted.

**Theorem 1.2 (Sum over every scalar center).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 and C0>=1 there is one K>0 that works for every prime p, real widths p^(3/2)<=X<=Y with XY<=C0*p^(18/5) and 6Y<p^2, and fixed alternating units a1,a2 modulo p^3. Sum, over every gamma modulo p^3 satisfying gamma*gamma=1, the number of six integer letters in the separate literal X,Y intervals whose existing sixReturnWord equals scalarReturn gamma. This entire sum is at most K*Y^2*p^epsilon. Real widths are interpreted by the proved membership of scalarSolutionsReal, so every integer tuple and its multiplicity is retained.

This existing public statement is preserved by applying prime_cube_scalar_return_count_of_exponent with alpha=18/5. The strengthened theorem above contains the complete counting assembly and proves the strict inequality 18/5<26/7 numerically. The result keeps its original hypotheses and conclusion.

The problem comes from Alexandru Pascadi, Non-abelian amplification and bilinear forms with Kloosterman sums, Geometric and Functional Analysis 36 (2026), 1174-1243, DOI 10.1007/s00039-026-00746-0; arXiv:2511.08445v2, Section 6, Conjecture 6.1 and Proposition 6.2. At c=p^3 and q=6, Proposition 6.2 gives Y^2(1+X^2/p^3) times p^o(1). For 3<alpha<26/7 and X=Y=p^(alpha/2), its extra factor is 1+p^(alpha-3), so that proposition does not directly give the whole strengthened range. The oracle broker suggested the cofactor elimination route and supplied literature leads; Codex derived and formalized the explicit degenerate quadratic branches, genuine-cubic factor improvement and complete count assembly. These are repository-derived results, not theorems attributed to Pascadi. The bounded literature screen found no covering theorem in the checked sources, but the final 2021 Shkredov primary-text comparison remains incomplete, and no priority claim follows. The unrestricted arbitrary-modulus conjecture remains open. Lean/kernel validation, accepted axiom closure and required repository checks determine formal delivery; this narrative is not a substitute for those checks.

The ordinary fixed-C0 fifteen-fourths endpoint.

The complete repository-derived ordinary proof is preserved in docs/develop/theory/PASCADI_PRIME_CUBE_PROJECTION_IDEAL_ENDPOINT.md, Theorem 1.1 and Sections 1-7. For every epsilon>0 and C0>=1 there is C(epsilon,C0)>0, uniform in every prime p, fixed units a1,a2 modulo p^3 and real widths p^(3/2)<=X<=Y with XY<=C0*p^(15/4) and 6Y<p^2, bounding the total literal six-letter count by C(epsilon,C0)*Y^2*p^epsilon. The word is the unchanged ordered product R(a1*h1)R(a2*h2)R(a1*h3)R(a2*h4)R(a1*h5)R(a2*h6), with odd letters in [-X,X], even letters in [-Y,Y], and the count summed over every scalar gamma with gamma squared equal to one. This includes the fixed-C0 endpoint and all strict alpha<15/4 ranges as ordinary mathematics.

The volume retains all original tuple multiplicities, one actual maximizing baseline at each middle, the six-chart and moment inputs, zero-reduction partners, the complete zero-D and rank-four cases, saturation and both coordinate-discriminant strata. The j=4 contribution keeps its separate all-layer argument, with threshold 233/61 and endpoint saving p^(-17/36) relative to A=XY. For the unramified nonsplit, rationally split and ramified j=3 cases, the primitive physical lattice gives D_L=plus-or-minus p^8*kappa, h divides kappa and n=abs(kappa)/h. The ramified ideal factor is (p)^4 of norm p^8 and is proved in the single ramified field, including conductor-order gluing. The raw determinant functional keeps its zero layer and the same actual baseline. The actual triple correlates h<<T and n<<K/T for K=C_D*A^7/p^26; the affine-plane argument counts ordered partners with weight p^eta*(1+(K/(h*n))^(1/3)).

The exact affine ideal coset keeps the rational coefficients of X_* in J^2. Five unit-safe shears give actual integer projection intervals of lengths O(TX), O(TY). Original middles use their short integer box and Gamma_0, with t modulo p^2 injective. Projections use the difference lattice Gamma_z=S_z*Gamma_0; its actual sheared witness need only lie in O(X) by O(Y). Shortest-vector counting applies to affine cosets through this difference lattice and retains split null directions. Long projection intervals are residue existence indicators, and one chosen lift injects residue support into the actual integer projection coset. Both Fourier slopes are units and may differ. This gives the fixed-data support bound p^eta*(T^2*A^2/p^6+p^(3/2)), without a U-lift or baseline multiplicity factor.

Generator pairs, unit cubes and ideal classes are counted with the published gcd-aware complete Kloosterman estimate in Pascadi, Lemma 3.3, Section 3.2, and Bhargava-Varma, The mean number of 3-torsion elements in the class groups and ideal groups of quadratic orders, Proceedings of the London Mathematical Society 112 (2016), 235-266, DOI 10.1112/plms/pdv062, Theorem 2(a),(b). The latter averages ordinary Picard-group 3-torsion over all quadratic orders of each sign, including nonmaximal orders; local restrictions are dropped before the mean, and rationally split orders receive a separate class count. Joint summation gives Y^2*p^eta*(A^12/p^45+A^10/p^(75/2)). Both area factors are bounded for fixed C0 at the endpoint; epsilon budgeting absorbs logarithms without a strict area saving. The original moment uses A^4/p^15<=C0^4. Separate width doubling, factor 64, all scalar centers, removed charts and bounded primes complete the ordinary statement.

This added narrative describes an ordinary proof and introduces no Lean declaration or new Describe.Lean. The current Lean total remains prime_cube_scalar_return_count_of_exponent with alpha<26/7; the earlier open-range sentences above describe that formal boundary. The four scoped zero-D results are integrated by merged PR #31431, commit 0997d09. Supplied evidence records successful required PR CI and first-dev CI still running at dispatch; no successful first-dev result is inferred. Their scoped statements do not certify this endpoint. Enlarged-range Lean, kernel or official acceptance, unrestricted-modulus resolution and completion of the main research goal are not claimed. The existing issue #31176 registration boundary is retained.

The owning Library/CharacterSums/pascadi2025nonabelianamplification.md note gives the exact mathematical-input declaration mappings and source identity: pascadi-prime-cube-projection-average.tex, SHA256 53c289cd83adeee1cdc34b4d61ac09ae1fbcb045f4985555d3b6314bdfeed30b. The full ordinary endpoint proof is repository-derived. The problem is Pascadi's; Kloosterman and Bhargava-Varma are attributed intermediate inputs. Derivative and global-arithmetic ideas came from prior Pro proposals and independently derived actual-family mathematics; the earlier Pro Section 2 error is repaired in the retained proof. Native Codex supplied implementation, derivations and independent ordinary-proof reviews with repository prior exposure. No model-family diversity or sterile independence is asserted. The bounded literature comparison found no covering theorem in its checked scope; final JNT 220 (2021), Lemma 15, DOI 10.1016/j.jnt.2020.06.014, remains unobtained and unverified and is not a proof input. No exhaustive novelty or global priority follows.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count_of_exponent`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates](PascadiOriginalRangeEstimates.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalRowReduction](PascadiOriginalRowReduction.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount](PascadiOriginalUnitMiddleCount.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiScalarCenters](PascadiScalarCenters.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSeventhHeightRange](PascadiSeventhHeightRange.md)
