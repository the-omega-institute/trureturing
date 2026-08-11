using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class DeficitThreeValuedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The normalized beta deficit of golden addition takes only the values -1, 0, and 1.",
        H("The Normalized Beta Deficit Is Three-Valued"),
        Blocks(
            Describe.Lean(DescribeId.Create("the-normalized-beta-deficit-is-three-valued"),
                DeclarationHandle.Create("D5/S1/Deficit/DeficitThreeValued.deficit_three_valued"),
                H("The normalized beta deficit takes only the values -1, 0, and 1"),
                StatementSource.FromAuthor(ThreeValuedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The deficit of golden addition is the failure of the model-set value "
                                        + "of canonical Zeckendorf digits to be additive across a sum: the "
                                        + "value of the first operand plus the value of the second minus the "
                                        + "value of the sum. The integer theorem of this bucket already "
                                        + "records that this deficit is a rational integer equal to the signed "
                                        + "count of bottom carries fired during normalization. This theorem "
                                        + "closes the remaining quantitative question: the integer is never "
                                        + "anything other than minus one, zero, or plus one. However large "
                                        + "the operands and however long the carry chain, the net hidden "
                                        + "account of normalization is at most a single unit.")),
                                    Paragraph(Text(
                                        "The proof intersects the integer certificate with a window bound on "
                                        + "the contraction face. Read on that face, each operand evaluates its "
                                        + "Zeckendorf indices at powers of the golden conjugate, whose "
                                        + "exponents are at least two. Splitting into even and odd exponents "
                                        + "dominates the positive part by the geometric series of the squared "
                                        + "conjugate starting at its square and the negative part by the same "
                                        + "series starting at its cube, so every reading lands in the window "
                                        + "from minus the inverse square of the golden ratio to the inverse of "
                                        + "the golden ratio. Three window readings place the deficit strictly "
                                        + "between minus two and two, and the final numeric gates reduce to "
                                        + "the golden conjugate being negative and the golden ratio being "
                                        + "less than two: the window of length exactly one admits precisely "
                                        + "three integers."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Deficit/DeficitInteger")),
        ]));

    private static Formula ThreeValuedFormula() =>
        Disp(Seq(
            F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, F.Id("v"),
            Underscore, D(2), Close, Sp, Eq, Sp,
            Beta, Apos, Open, F.Id("v"), Underscore, D(1), Close, Sp, Plus, Sp,
            Beta, Apos, Open, F.Id("v"), Underscore, D(2), Close, Sp, Minus, Sp,
            Beta, Apos, Open, F.Id("v"), Underscore, D(1), Plus, F.Id("v"),
            Underscore, D(2), Close, Sp, InMacro, Sp,
            OpenBrace, Minus, D(1), Comma, Sp, D(0), Comma, Sp, Plus, D(1),
            CloseBrace));
}
