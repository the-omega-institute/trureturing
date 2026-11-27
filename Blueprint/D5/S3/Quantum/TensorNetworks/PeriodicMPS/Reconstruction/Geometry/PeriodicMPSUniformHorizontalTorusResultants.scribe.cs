using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalTorusResultantsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalTorusResultants";
    private const string Title = "Resultants in the two torus coordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontaltorusresultants-height-one-torus-prime-cannot-contain-axis-resultants"),
                DeclarationHandle.Create(Module + ".height_one_torus_prime_cannot_contain_axis_resultants"),
                H("Laurent polynomials on the two axes exclude height one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After clearing Laurent powers, the prime contains a nonzero polynomial in each separate coordinate. The two projected resultant tests are nonzero because one input in each test is a nonzero constant over the other-coordinate fraction field."))),
                DescribeRole.Theorem))));
}
