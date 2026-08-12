using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class ClassicalAnswerTableExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One preparation-independent deterministic answer table is excluded by both "
            + "noncontextual and local witnesses.",
        H("Double Exclusion of a Classical Answer Table"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                                    "one-preparation-independent-answer-table-is-doubly-excluded"),
                DeclarationHandle.Create("D5/S3/Observer/ClassicalAnswerTableExclusion.noncontextual_and_local_double_exclusion"),
                H("One preparation-independent answer table is doubly excluded"),
                StatementSource.FromAuthor(DoubleExclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let Fiber be finite and nonempty. One deterministic answer-table structure "
                                        + "contains total answer functions covering every element of the "
                                        + "two-dimensional window algebra and Alice's and Bob's two CHSH settings. "
                                        + "These functions have no preparation argument. A finite preparation "
                                        + "supplies only one nonnegative normalized weight on Fiber, shared by all "
                                        + "four settings.")),
                                    Paragraph(Text(
                                        "For the noncontextual branch, suppose that the values assigned by this same "
                                        + "table at each fiber extend to one unital complex-algebra character on the "
                                        + "complete window algebra. Choosing any fiber produces a character on the "
                                        + "two-by-two matrix algebra, contradicting WindowCharacter."
                                        + "window_algebra_has_no_character at window size two.")),
                                    Paragraph(Text(
                                        "For the local branch, localModel reads Alice's and Bob's Boolean answers "
                                        + "from that same table instance. ClassicalFiberBound."
                                        + "classical_chsh_abs_le_two bounds the absolute weighted CHSH value by two. "
                                        + "The frozen Bell witness is positive two times square root two, which is "
                                        + "strictly greater than two, so the table cannot reproduce it.")),
                                    Paragraph(Text(
                                        "The Lean conclusion is the conjunction of the two negations for one named "
                                        + "table T, not a conjunction of unrelated witness facts. The theorem is "
                                        + "limited to finite nonempty fibers, the complete size-two window algebra, "
                                        + "and the fixed Bell-state CHSH witness. It asserts no general Kochen-Specker "
                                        + "classification, infinite hidden-variable theorem, or quartic-context "
                                        + "obstruction."))),
                DescribeRole.Theorem
            ))));

    private static Formula DoubleExclusionFormula() => Disp(Seq(
        Forall, Sp, F.Id("T"), Comma, RowBreak, Sp,
        Neg, Sp, Operatorname, Grp(F.Id("Noncontextual")), Open, F.Id("T"), Close,
        Sp, Land, Sp,
        Neg, Sp, Operatorname, Grp(F.Id("ReproducesBellCHSH")),
        Underscore, Grp(Mu), Open, F.Id("T"), Close, Dot));
}
