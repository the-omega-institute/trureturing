using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class GaussianLaplaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/GaussianLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The forward response regular term satisfies the wider strip bounds for Gaussian inversion.",
        H("Gaussian strip bounds for the forward Laplace transform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-paired-laplace-gaussian-strip"),
                DeclarationHandle.Create(Prefix + "forwardPairedLaplaceData_gaussianStrip"),
                H("Wider holomorphy and quadratic vertical growth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the Riemann hypothesis, the von Koch bound and the paired "
                    + "xi expansion. For the logarithmic forward response cut off at log(3), "
                    + "the regular term of its paired Laplace representation is holomorphic "
                    + "on -1/5 < Re(s) < 1 and has a uniform quadratic vertical bound on "
                    + "-1/6 <= Re(s) <= 3/4. Use the same Mellin remainder as in that "
                    + "representation, with strip margin 1/30. The digamma argument "
                    + "(s + 1/2)/2 has real part between 1/6 and 5/8; the Binet estimate "
                    + "and the complex logarithm bound control its growth. The rational "
                    + "term 1/(2(s + 1/2)) is bounded by three on this strip."))),
                DescribeRole.Theorem))));
}
