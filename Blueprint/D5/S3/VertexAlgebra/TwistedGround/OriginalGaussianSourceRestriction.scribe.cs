using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceRestrictionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianSourceRestriction", H("Frequency restriction after full inverse colour transport"), Blocks(
            Paragraph(Text("The inverse substitution is diagonal only in frequency. At each frequency its action still sums over every original colour. Expanding this action proves that full right covariance and opposite-charge mean entries restrict across nested frequency boxes. Both mixed rectangles and the external block are included. Native affine coefficient enlargement then gives full-row stabilization while retaining each external occupation in its row degree. Empty colour, frequency and external types are in scope. The original Wick contraction is also reduced to one arbitrary common box that contains the fixed external supports and the energy layer. The external analytic coefficient extraction remains separate.")),
            Describe.Lean(DescribeId.Create("original-source-internal-inclusion"), DeclarationHandle.Create(Prefix + "internalInclusion"), H("Colour-preserving frequency inclusion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The embedding retains every colour and the value of each positive frequency in a larger frequency box."))), DescribeRole.Definition),
            N("original_right_covariance_restrict", "Complete transported covariance restriction", "All four internal and external block cases use the actual complete inverse colour transport before restriction. The finite colour sums are identical at retained frequencies."),
            N("original_right_mean_restrict", "Opposite-charge mean restriction", "The complete inverse transport of the original mean at charge minus a commutes with nested frequency-box restriction."),
            N("original_row_coefficients_restrict", "Actual native row coefficient stabilization", "Both full affine row coefficients are preserved by the internal frequency inclusion and the identity on external coordinates. The right equality consumes the full transported covariance and mean restriction results; external degrees remain literal."),
            N("original_row_energy_layer_stabilizes", "Finite source energy stabilization", "Every occupation at energy n has positive frequencies at most n. The colour-preserving inclusion is therefore a bijection on energy layers once the cutoff is at least n. Native row restriction and invariance of the single internal factorial preserve the energy sum, including its zero-energy layer."),
            N("original_fixed_energy_common_box", "Original Wick contraction in one common box", "For every common box strictly larger than n and containing all four external supports, the original fixed-energy Wick contraction equals its native affine energy layer. Both charge scalars, all four external factorials and both integer Laurent selectors remain literal. The right covariance and opposite-charge mean use the complete original inverse colour transport before any restriction.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-gaussian-sourcerestriction-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
