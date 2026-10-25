using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class SignedRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/SignedRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed remainder limit.",
        H("The signed remainder limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-remainder-tendsto"),
                DeclarationHandle.Create(Prefix + "signed_remainder_tendsto"),
                H("The signed remainder limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume alpha>=0 and an eventual bound |E(t)|<=C*t^alpha. For a>=3, sigma>alpha-7/10 and A>=0, suppose r has derivative dr on [a,infinity), dr is almost everywhere strongly measurable there, and the bounds |r(t)|<=A*t^(-sigma-7/10), |dr(t)|<=A*t^(-sigma-17/10) hold. Then sum(Lambda(n)*r(n),floor(a)<n<=floor(b))-integral_a^b r(t) dt tends to -E(a)*r(a)-integral_a^infinity E(t)*dr(t) dt. Finite Abel summation preserves all prime powers and the stated bounds send the final endpoint to zero."))),
                DescribeRole.Theorem))));
}
