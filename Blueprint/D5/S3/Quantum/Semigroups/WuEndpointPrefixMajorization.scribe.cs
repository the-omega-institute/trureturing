using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointPrefixMajorizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered spectrum of the signed map is majorized by classical two-bit noise on the input spectrum.",
        H("Spectral majorization at the Wu endpoint"),
        Blocks(
            Paragraph(Text("Expanding a Hermitian input in terms of its three proper spectral prefix projections and the identity gives nonnegative coefficients for the projection terms. The projection bounds control each trace pairing. Applying this estimate to the ordered output eigenbasis yields the three spectral prefix inequalities, and trace preservation gives equality for the full sum.")),
            Paragraph(Text("For every Hermitian two-mode matrix, the sum of the largest k output eigenvalues is at most the sum of the first k entries of the classical two-bit noise applied to the ordered input eigenvalues, for k equal to one, two or three (`A₁_spectral_prefix`).")),
            Paragraph(Text("For every Hermitian two-mode input, the classical comparison vector is decreasing, it dominates all three proper output spectral prefixes, and its total sum equals the total output eigenvalue sum (`A₁_spectral_majorization`).")),
            Describe.Lean(DescribeId.Create("classical-order"), DeclarationHandle.Create(Owner + "endpointClassical_antitone"),
                H("Order of the classical comparison vector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The classical two-bit noise transform sends every decreasing four-vector to a decreasing four-vector."))), DescribeRole.Theorem))));
}
