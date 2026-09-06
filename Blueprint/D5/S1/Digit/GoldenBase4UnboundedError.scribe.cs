using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4UnboundedErrorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/GoldenBase4UnboundedError.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An anchored typed machine below twenty-one states must disagree with the exact golden digit function on legal inputs of unbounded nonzero-digit count.",
        H("Unbounded Arithmetic Error Weight Below Twenty-One States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-base4-high-weight-collision"),
                DeclarationHandle.Create(Prefix + "high_weight_collision"),
                H("High-weight collisions determine the reference state"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Above a fixed nonzero-digit threshold, agreement on all legal inputs and equality of candidate states imply equality of reference states. The proof uses typing and thirteen finite diagnostic suffixes. It does not assume agreement on unobserved words from agreement only on powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base4-bounded-error-needs-21"),
                DeclarationHandle.Create(Prefix + "bounded_error_weight_requires_twenty_one"),
                H("Bounded-weight disagreement cannot reduce the anchored state count"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The word 00001 is a one-containing loop at reference state 18. Repeating it gives arbitrarily high-weight access to all twenty noninitial states. Finite separation forces twenty different candidate states. None can be the initial state, because that state is fixed by zero and none of the twenty core states is. An injection from Option (Fin 20) proves the count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base4-small-unbounded-error"),
                DeclarationHandle.Create(Prefix + "small_machine_unbounded_error_weight"),
                H("Every smaller anchored machine has unbounded-weight disagreements"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each bound on the number of ones there is a legal reference input above that bound on which the candidate differs or is undefined. The input is not required to be a power of four. This excludes one proposed certification route without asserting the powers-only minimum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base4-small-unbounded-arithmetic-error"),
                DeclarationHandle.Create(Prefix + "small_machine_unbounded_arithmetic_errors"),
                H("The reference label is the exact arithmetic floor difference"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing successful_run_digit theorem identifies the mismatched label with the exact floor difference at the input's Fibonacci value. No numerical oracle, external Diophantine assumption or analytic density result is used in this proof."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S1/Digit/GoldenBase4IntervalMachine"))]));
}
