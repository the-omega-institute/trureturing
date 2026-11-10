using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class DiscreteMomentAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discrete moment stage consumes the weighted arithmetic transfer and formal interval bounds.",
        H("Discrete moment asymptotic inputs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discrete-moment-asymptotic-inputs"),
                DeclarationHandle.Create(Prefix + "discrete_moment_asymptotic_inputs"),
                H("Arithmetic and formal moment envelopes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume zero less than alpha less than beta less than one, normalized singular-series values on the empty set and singletons, the four-point mean-square correlation bound and interval correlation estimates. For every endpoint window M>=1 and positive epsilon, weighted discrete cubic and fourth moments have a uniform arithmetic transfer error of size C B N to the power one half plus epsilon times H to the moment order. The formal cubic and fourth envelopes share a nonnegative modulus, antitone from two and tending to zero, uniformly for lengths in the prescribed power band and logarithms in the dyadic window."))),
                DescribeRole.Theorem))));
}
