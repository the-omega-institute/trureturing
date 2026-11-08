using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentEndpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local fourth energy controls normalized moving and frozen increments.",
        H("Fourth-moment endpoint estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-fourth-endpoint-bound"),
                DeclarationHandle.Create(Prefix + "local_fourth_endpoint_bound"),
                H("Fourth energy between moving endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the fourth powers of fixed increments have local energy at most C times v squared times log(X) squared times the window length plus the uniform error. For increasing endpoint functions with derivatives at least m and signed gap at most R, their fourth-power difference integral is at most (656/3)(C/m)R squared log(X) squared times the image interval length plus the error. Averaging the common-endpoint identity over [2R,3R] and [R,4R] uses the shared even-power endpoint estimate. The two quadratic integrals sum to (82/3)R cubed, giving exactly 656/3."))),
                DescribeRole.Theorem))));
}
