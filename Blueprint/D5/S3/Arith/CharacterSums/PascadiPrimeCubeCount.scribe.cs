using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiPrimeCubeCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original alternating six-return count in a prime-cube area range, with every scalar involution center and every prime retained.",
        H("The literal prime-cube six-return count"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-cube-scalar-return-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount.prime_cube_scalar_return_count"),
                H("Sum over every scalar center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0 and C0>=1 there is one K>0 that works for every prime p, real widths p^(3/2)<=X<=Y with XY<=C0*p^(18/5) and 6Y<p^2, and fixed alternating units a1,a2 modulo p^3. Sum, over every gamma modulo p^3 satisfying gamma*gamma=1, the number of six integer letters in the separate literal X,Y intervals whose existing sixReturnWord equals scalarReturn gamma. This entire sum is at most K*Y^2*p^epsilon. Real widths are interpreted by the proved membership of scalarSolutionsReal, so every integer tuple and its multiplicity is retained.")),
                    Paragraph(Text("For large p apply actual_unit_middle_tuple_count with epsilon/2 to the actual unit-middle subset of the original minus-identity solutions. Its six filtered branches choose the same actual reduced basis at each occupied middle pair and impose no branch restrictions on the input set. Set H=sqrt(XY). The original area cap supplies all three numerical cutoffs through original_range_numeric_cutoffs, and original_range_error_absorption proves the logarithm and square-root terms are bounded by a constant times XY*p^epsilon. Nminus_le_three_Uminus_of_three_width then restores every nonunit row under 3Y<p^2; its sharper cutoff is essential after the all-center comparison doubles the widths.")),
                    Paragraph(Text("Apply scalarSolutionsReal_card_le_minus_doubled at X,Y, then apply the minus estimate at 2X,2Y with area constant 4C0. Its actual interval floors only enter the finite row reduction; the unit-middle bound keeps the physical real widths, so no false floor lower bound is assumed. Odd prime-power units are cyclic, and their square kernel has at most two elements; for p=2 all involutions inject into the four units modulo eight. Thus the sum over all centers costs at most four times the single-center estimate. For primes below the explicit cutoff P=(2^20*(1+4C0))^200, use the literal count at most 729Y^6 and Y<=P^2, giving at most 2916P^8*Y^2*p^epsilon. There is no excluded small prime or uncounted zero, row, endpoint or scalar center."))),
                DescribeRole.Theorem),
            Paragraph(Text("The problem comes from Alexandru Pascadi, Non-abelian amplification and bilinear forms with Kloosterman sums, Geometric and Functional Analysis 36 (2026), 1174-1243, DOI 10.1007/s00039-026-00746-0; arXiv:2511.08445v2, Section 6, Conjecture 6.1 and Proposition 6.2. At c=p^3 and q=6, Proposition 6.2 gives Y^2(1+X^2/p^3) times p^o(1). Its extra factor grows as p^(3/5) at X=Y=p^(9/5), so that proposition does not directly yield the entire range proved here. The result above is a repository-derived proof of this precise prime-cube slice, not a theorem attributed to Pascadi. It does not assert the unrestricted arbitrary-modulus conjecture or establish literature priority; the final Shkredov/Chang primary-text comparison remains incomplete. Lean/kernel validation, the accepted axiom closure and required repository checks determine formal delivery; this narrative is not a substitute for those checks.")))));
}
