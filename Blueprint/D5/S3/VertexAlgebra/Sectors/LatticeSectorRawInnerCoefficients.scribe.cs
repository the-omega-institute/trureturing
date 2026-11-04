using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorRawInnerCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorRawInnerCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual raw canonical inner coefficients", H("Actual raw canonical inner coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("actual-three-field-raw-inner-coefficients"),
                DeclarationHandle.Create(Prefix + "actual_three_field_raw_inner_coefficients"),
                H("Reconstruction with the original locality and numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, charges and oscillator descendants, choose k before the fourth charge and state. The same original statewise bounds a and generally infinite common numerator P retain canonical truncation and all six signed product laws. The already cleared inner iterate equals P under the legal native collision (x,b+z,z). The literal original polynomial action is derived from clearedInnerIterate through the accepted finite expansion. The actual canonical inner coefficient u_x((v_b t)_z w) equals the finite three-index sum in innerCollision P, with inputs (x+a0+2k+r+j,b+k-r-l,z+a1+a2-j+l) and weights (-1)^(r+j) binom(-k,r) binom(-(2k+r),j) binom(-a1,l). All three inputs are filtered for nonnegativity; r,l <= b+k and j <= b+z+k+a1+a2 are containing bounds. Actual truncation of v on t gives a uniform lower b bound. For each fixed b, actual truncation of v_b t on w gives a lower z bound uniform in x. Supported injectivity then identifies the actual channel with the proved inverse. All signed targets, the zero numerator, repeated charges, rank zero and indefinite lattice data remain included. No finite numerator, domain, positivity, charge, energy or assumed raw-action identity is required. The suppliers retain Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution and the canonical normalization. This is one inner reconstruction; it asserts no five-bracketing common numerator, pentagon, analytic convergence or physical realization."))), DescribeRole.Theorem))));
}
