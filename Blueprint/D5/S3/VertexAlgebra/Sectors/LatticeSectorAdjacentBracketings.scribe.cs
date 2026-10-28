using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorAdjacentBracketingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent canonical bracketings", H("Adjacent canonical bracketings"), Blocks(
            Describe.Lean(DescribeId.Create("adjacent-canonical-bracketings"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorAdjacentBracketings.actual_three_field_adjacent_bracketings"),
                H("actual_three_field_adjacent_bracketings"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, charges and descendant states, choose one locality order k before the fourth charge and state. The same statewise bounds a and generally infinite numerator P retain canonical truncation and all six signed product laws. In the chamber b << s << z, the actual u(vt) channel followed by its outer action on w equals the finite sum over middleFiber, with scalar (-1)^j binom(-k,j) binom(-a1,l) binom(-a0,q) and numerator indices (s+2k+j-q,b+k-j-l,z+a0+a1+a2+q+l). Every numerator coordinate is filtered for nonnegativity; the containing bounds are j,l <= b+k and q <= s+b+3k. The numerator is P composed with (s+z,b+z,z). Actual truncation gives a uniform lower b bound and a lower s bound for each fixed b, uniform in z. Supported positive inversion removes the remaining s+z factor, then two supported inversions remove y+z and s-y; the native numerator kills all artificial tails, including the negative signed branches. The literal middle polynomial action equals this middle numerator. The final polynomial action on the actual (uv)t channel equals P composed with (x+y+z,y+z,z), and the actual final channel equals its existing Laurent coefficient with the same k and a. Legal substitution relates the two native numerators; the raw coefficients in distinct chambers are not identified at unchanged indices. The frozen normalization and final covariance are reused. Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution remains in the suppliers. No finite numerator, positivity, energy, new charge restriction or assumed channel comparison is used. These formal coefficient identities assert no analytic or physical realization."))), DescribeRole.Theorem))));
}
