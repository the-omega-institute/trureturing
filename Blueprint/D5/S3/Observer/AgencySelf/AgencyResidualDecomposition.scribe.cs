using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencyResidualDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencySelf/AgencyResidualDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The current-state kernel decomposes into completed and strategy-residual pairs.",
        H("Agency Residual Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-current-relation-splits-into-completed-or-residual-pairs"),
                DeclarationHandle.Create(Prefix + "current_relation_decomposition"),
                H("The current relation splits into completed or residual pairs"),
                StatementSource.FromAuthor(DecompositionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix current and profile readouts and two histories. Equality under the "
                            + "current readout admits a case split on profile equality.")),
                    Paragraph(Text(
                        "If profile values agree, the pair is completion-related; otherwise it "
                            + "lies in the agency residual. Either branch retains current-state "
                            + "equality.")),
                    Paragraph(Text(
                        "The disjunction is exhaustive for the displayed pair and makes no claim "
                            + "that one branch is globally inhabited."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completed-and-residual-pairs-are-disjoint"),
                DeclarationHandle.Create(Prefix + "completion_residual_exclusive"),
                H("Completed and residual pairs are disjoint"),
                StatementSource.FromAuthor(ExclusivityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A completion-related pair has equal profile values, whereas an agency "
                            + "residual pair has unequal profile values.")),
                    Paragraph(Text(
                        "The same pair cannot satisfy both predicates, so their conjunction is "
                            + "logically impossible."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion) =>
        Disp(Seq(
            Forall, Sp, F.Id("current"), Colon, Sp,
            Arrow(F.Id("H"), F.Id("M")), Comma, Sp,
            F.Id("profile"), Colon, Sp, Arrow(F.Id("H"), F.Id("P")), Comma, Sp,
            F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("H"), Comma, Sp,
            conclusion, Dot));

    private static Formula DecompositionStatement()
    {
        Formula completed = Call("CompletionRelated", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        Formula residual = Call("AgencyResidual", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        Formula split = Seq(Open, completed, Sp, Lor, Sp, residual, Close);
        return PrefixFormula(Seq(
            Call("SameUnder", F.Id("current"), F.Id("x"), F.Id("y")),
            Sp, Iff, Sp, split));
    }

    private static Formula ExclusivityStatement()
    {
        Formula completed = Call("CompletionRelated", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        Formula residual = Call("AgencyResidual", F.Id("current"),
            F.Id("profile"), F.Id("x"), F.Id("y"));
        return PrefixFormula(Seq(Neg, Open, completed, Sp, Land, Sp, residual, Close));
    }
}
