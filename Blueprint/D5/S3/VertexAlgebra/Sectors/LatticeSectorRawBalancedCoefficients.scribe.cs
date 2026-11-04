using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorRawBalancedCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorRawBalancedCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual raw balanced reconstruction", H("Actual raw balanced reconstruction"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorrawbalancedcoefficients-actual-three-field-raw-balanced-coefficients"),
                DeclarationHandle.Create(Prefix + "actual_three_field_raw_balanced_coefficients"),
                H("Actual raw balanced reconstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, charges and oscillator states, the same locality order k is chosen before the fourth charge and state. The same original bounds a and generally infinite P retain canonical truncation, all six signed product laws, inner cleared and action identities, the finite raw inner formula, actual balanced support and balanced clearing. The actual balanced channel is canonical of the first pair acting on the second pair, in tree ((uv)(tw)). Its coefficient equals the finite three-index formula for the same native numerator P(s+x,x,z). Uniform s support comes from truncation of u on v and uniform z support from truncation of t on w; both are uniform in x. Literal polynomial action is proved from the finite balanced clearing and then cancelled on this actual support. No finite numerator, x cutoff, domain, energy, positivity or charge restriction is required. Bakalov--Kac, Matsuo--Nagatomo and Carnahan supplier attributions and canonical normalization are preserved."))), DescribeRole.Theorem))));
}
