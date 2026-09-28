using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MultiplierOrbitMomentSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MultiplierOrbitMomentSelection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative invariance imposes a selection rule on arithmetic power moments.",
        H("Multiplier-Orbit Moment Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-sum-zero-of-mul-invariant"),
                DeclarationHandle.Create(Prefix + "power_sum_zero_of_mul_invariant"),
                H("Nontrivial multiplier moments vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a nonzero field element multiply a finite set onto itself. "
                        + "Reindexing its kth power sum by this permutation multiplies the "
                        + "same sum by the kth power of the multiplier. When that scalar is "
                        + "not one, cancellation in the field forces the sum to vanish. "
                        + "The result applies to invariant subsets, without requiring the "
                        + "whole field or a free action."))),
                DescribeRole.Theorem))));
}
