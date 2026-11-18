using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiPrimeCubeCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original alternating six-return count in a prime-cube area range, with every scalar involution center and every prime retained.",
        H("The literal prime-cube six-return count"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-cube-scalar-return-count-of-exponent"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count_of_exponent"),
                H("Every fixed area exponent below twenty-six sevenths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0, C0>=1 and fixed real alpha<26/7 there is one K>0, independent of the prime, the widths and the alternating units, such that the total literal six-letter count is at most K*Y^2*p^epsilon whenever p^(3/2)<=X<=Y, XY<=C0*p^alpha and 6Y<p^2. The count sums over every gamma modulo p^3 with gamma squared equal to one. There is no supplied chart, lattice estimate or count; all integer rows, ordered multiplicities, zero and nonunit branches and small primes are retained.")),
                    Paragraph(Text("The structural actual degree-two resultant has seventh weighted height. A quadratic factor of a genuine cubic gains an extra J/I, and its mixed resultant has sixth weighted height; the cubic residual still has seventh weighted height. PascadiSeventhHeightCover combines all of these branches. The actual coordinate product is at most 32XY/p^3, so a fixed seventh-height constant times its seventh power is below p^5 for every sufficiently large prime precisely when alpha<26/7. The enlarged number-field value envelope uses T=p^2 and epsilon/2, keeping one field-uniform p^epsilon constant without the old cubic-height cutoff. The zero-reduction branches require only the small-height consequences already forced by this seventh-height gap.")),
                    Paragraph(Text("The actual bad-degree average, retained-record count and six-branch unit-middle assembly consume these bounds. The moment error is absorbed for every alpha<=15/4, which includes alpha<26/7. Apply the all-center comparison at 2X,2Y with area constant 4C0, restore nonunit rows under 3*(2Y)<p^2, and sum over at most four scalar centers. Below the positive threshold P supplied by seventh_area_height_cutoff, the literal bound 729Y^6 and Y<=P^2 give a uniform multiple of Y^2*p^epsilon. Neither alpha=26/7 nor unrestricted moduli are asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-cube-scalar-return-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count"),
                H("Sum over every scalar center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0 and C0>=1 there is one K>0 that works for every prime p, real widths p^(3/2)<=X<=Y with XY<=C0*p^(18/5) and 6Y<p^2, and fixed alternating units a1,a2 modulo p^3. Sum, over every gamma modulo p^3 satisfying gamma*gamma=1, the number of six integer letters in the separate literal X,Y intervals whose existing sixReturnWord equals scalarReturn gamma. This entire sum is at most K*Y^2*p^epsilon. Real widths are interpreted by the proved membership of scalarSolutionsReal, so every integer tuple and its multiplicity is retained.")),
                    Paragraph(Text("This existing public statement is preserved by applying prime_cube_scalar_return_count_of_exponent with alpha=18/5. The strengthened theorem above contains the complete counting assembly and proves the strict inequality 18/5<26/7 numerically. The result keeps its original hypotheses and conclusion."))),
                DescribeRole.Theorem),
            Paragraph(Text("The problem comes from Alexandru Pascadi, Non-abelian amplification and bilinear forms with Kloosterman sums, Geometric and Functional Analysis 36 (2026), 1174-1243, DOI 10.1007/s00039-026-00746-0; arXiv:2511.08445v2, Section 6, Conjecture 6.1 and Proposition 6.2. At c=p^3 and q=6, Proposition 6.2 gives Y^2(1+X^2/p^3) times p^o(1). For 3<alpha<26/7 and X=Y=p^(alpha/2), its extra factor is 1+p^(alpha-3), so that proposition does not directly give the whole strengthened range. The oracle broker suggested the cofactor elimination route and supplied literature leads; Codex derived and formalized the explicit degenerate quadratic branches, genuine-cubic factor improvement and complete count assembly. These are repository-derived results, not theorems attributed to Pascadi. The bounded literature screen found no covering theorem in the checked sources, but the final 2021 Shkredov primary-text comparison remains incomplete, and no priority claim follows. The unrestricted arbitrary-modulus conjecture remains open. Lean/kernel validation, accepted axiom closure and required repository checks determine formal delivery; this narrative is not a substitute for those checks.")))));
}
