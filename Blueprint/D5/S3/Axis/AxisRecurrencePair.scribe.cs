using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisRecurrencePairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var W = Id("W");
        var t = Id("t");
        var K = Id("K");

        var sumStep = Equal(
            Call("W", Add(K, Num(2))),
            Add(Call("W", Add(K, Num(1))),
                Multiply(Call("t", Add(K, Num(2))), Call("W", K))));

        var weightStep = Equal(
            Call("t", Add(K, Num(2))),
            Multiply(Call("t", Add(K, Num(1))), Call("t", K)));

        var pair = new Formula.Logic(sumStep, FormulaLogicOperator.And, weightStep);

        const string declarationPrefix = "D5/S3/Axis/AxisRecurrencePair.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The partial sum and the weight satisfy their two recurrences together.",
            H("Axis Recurrence Pair"),
            Blocks(
                Paragraph(Text(
                    "The axis partial sum collects the legal words up to a given digit depth, "
                        + "and the axis weight reads the two Galois embeddings at that depth. "
                        + "Each satisfies its own two step recurrence: the sum steps by adding "
                        + "the sum two depths back, weighted by the next weight, and the "
                        + "weights compose multiplicatively.")),
                Paragraph(Text(
                    "Both halves were already proved separately. What did not exist was a "
                        + "statement that they hold of the same pair of sequences at the same "
                        + "depth, which is what the source records as one closed recurrence. "
                        + "Neither half is restated here; the conjunction is the content.")),
                Describe.Lean(
                    DescribeId.Create("the-two-recurrences-hold-of-the-same-pair"),
                    DeclarationHandle.Create(declarationPrefix + "axis_recurrence_pair"),
                    H("The two recurrences hold of the same pair"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pair)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The sum recurrence follows from splitting a legal word on its highest "
                            + "digit, which forces the digit below it to be empty; the weight "
                            + "recurrence follows because both embeddings satisfy the same "
                            + "quadratic, so their powers are additively Fibonacci and the "
                            + "exponential turns that into a product."))),
                    DescribeRole.Theorem))));
    }
}
