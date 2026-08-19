using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisTraceRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The axis weight is multiplicatively Fibonacci, so consecutive weights compose.",
        H("Axis Trace Recurrence"),
        Blocks(
            Paragraph(Text(
                "The axis weight reads a depth at both Galois embeddings at once. Its exponent "
                    + "is a linear combination of a golden power and its conjugate, and both "
                    + "powers satisfy the same two-step recurrence, so the exponent is additively "
                    + "Fibonacci and the weight itself is multiplicatively so.")),
            Paragraph(Text(
                "The conjugate step is proved here from its defining quadratic rather than "
                    + "assumed by symmetry: the golden ratio has an upstream power lemma, the "
                    + "conjugate does not, and the two embeddings are not interchangeable in "
                    + "general even though this particular identity holds for both.")),
            Describe.Lean(
                DescribeId.Create("axis-weight-is-multiplicatively-fibonacci"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/AxisTraceRecurrence."
                        + "axis_weight_is_multiplicatively_fibonacci"),
                H("The axis weight is multiplicatively Fibonacci"),
                StatementSource.FromAuthor(WeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed conjunct is the composition law; the package also carries "
                        + "positivity at every depth and the base value."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Axis/LambdaMinusDirichletSeries")),
        ]));

    private static Formula Weight(Formula index) =>
        Seq(F.Id("t"), Underscore, Grp(index));

    private static Formula WeightFormula()
    {
        Formula k = F.Id("K");

        return Disp(Seq(
            Forall, Sp, k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Weight(Seq(k, Plus, D(2))), Sp, Eq, Sp,
            Weight(Seq(k, Plus, D(1))), Sp, Cdot, Sp, Weight(k), Dot));
    }
}
