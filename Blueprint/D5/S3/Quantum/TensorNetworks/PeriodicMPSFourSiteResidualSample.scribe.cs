using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteResidualSampleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree-eight residual quotient certificate in characteristic five",
        H("Residual equations at a four-site specialization"),
        Blocks(
            Theorem("sample_necklace_values", "The specialization comes from actual tensors",
                "Taking the six necklace traces of two explicit pairs of binary bond-two tensors gives the source triplet matrices over the field with five elements."),
            Theorem("sample_pencil_decompositions", "Coefficient identities for the two pencils",
                "Over any commutative ring of characteristic five, the two sextics decompose into a cubic product equation times a cubic and a determinant divisor times a conic. Adjugate substitution on the second conic gives a quartic in the first pencil."),
            Theorem("residual_sample_degree_eight_rank", "A one-dimensional bound at degree eight",
                "In the homogeneous quotient by the cubic, conic and quartic, reductions send every degree-eight monomial into the span of the eighth power of the first coordinate. This bounds the degree-eight quotient image over every field of characteristic five."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-sample-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
