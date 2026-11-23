using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibMarginalExtensionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension.extendible_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common-state criterion for two adjacent marginals on three Fibonacci sites.",
        H("Positive extension of adjacent Fibonacci marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-marginal-extension"),
                DeclarationHandle.Create(Result), H("The minimum endpoint-pair weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On three sites with adjacent occupation forbidden the legal words are "
                    + "the vacuum, the three singleton words, and the pair of occupied endpoints. "
                    + "Measure the two adjacent edges. Each edge state has a vacuum entry and a "
                    + "two-dimensional singleton block. Entries between the vacuum and singleton "
                    + "sectors are zero. Let the occupations be pA, pB and pC, "
                    + "with the same pB in both edge states. Let alpha and beta be the complex "
                    + "entries from the middle singleton column to the endpoint singleton row.")),
                    Paragraph(Text(
                    "Put q0 equal to the larger of zero and pA + pB + pC - 1. A common "
                    + "positive semidefinite trace-one state exists exactly when pB is "
                    + "nonnegative, both endpoint occupations are at least q0, and the two "
                    + "squared coherence moduli are at most pB × (pA - q0) and "
                    + "pB × (pC - q0), respectively.")),
                    Paragraph(Text(
                    "The actual endpoint-pair weight q is at least q0 by positivity of the "
                    + "vacuum weight. The two specified principal minors of the singleton block "
                    + "then give the necessary coherence bounds. For sufficiency choose q0. "
                    + "With positive central weight, one outer product supplies both specified "
                    + "coherences, and nonnegative diagonal residuals supply the remaining "
                    + "endpoint singleton weights. With zero central weight both coherences "
                    + "vanish. Completing by the vacuum and endpoint-pair weights gives a "
                    + "trace-one state with both required partial traces."))),
                DescribeRole.Theorem))));
}
