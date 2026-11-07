using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class WeightedPrimitiveBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform primitive bound controls integration against a smooth real weight.",
        H("Weighted primitive estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-integral-le-of-primitive-bound"),
                DeclarationHandle.Create(Prefix + "weighted_integral_le_of_primitive_bound"),
                H("Transferring a primitive bound through a weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A<=B, let f be integrable on [A,B], and let W be "
                    + "continuously differentiable there. Suppose K>=0 and "
                    + "the primitive F(y)=integral from A to y of f has "
                    + "absolute value at most K throughout [A,B]. Then the "
                    + "absolute value of the integral of W*f is at most "
                    + "K times the sum of |W(B)| and the integral of |W'|. "
                    + "The primitive is absolutely continuous and has derivative "
                    + "f almost everywhere. Integration by parts for absolutely "
                    + "continuous functions gives W(B)*F(B) minus the integral "
                    + "of W'*F, since F(A)=0. The primitive bound controls both terms."))),
                DescribeRole.Theorem))));
}
