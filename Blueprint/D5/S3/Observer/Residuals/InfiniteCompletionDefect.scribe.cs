using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Residuals;

internal sealed class InfiniteCompletionDefectDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Residuals/InfiniteCompletionDefect."
            + "infinite_completion_defect_eq_zero_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive weighted defect series vanishes exactly when every finite defect vanishes.",
        H("Infinite Completion Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("infinite-completion-defect-zero-characterization"),
            DeclarationHandle.Create(Declaration),
            H("The infinite defect detects every finite defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let each state have a nonnegative real defect at every finite layer. "
                        + "Construct one scalar by normalizing each defect and weighting layer "
                        + "n by two to the negative n-plus-one power.")),
                Paragraph(Text(
                    "The normalized terms are nonnegative and bounded by a summable geometric "
                        + "series. If their total is zero, each individual term is zero, and "
                        + "the positive weights and denominators recover the original defects.")),
                Paragraph(Text(
                    "Repository searches found no prior normalized defect construction. The "
                        + "pinned library supplies the geometric summability and ordered-sum "
                        + "comparison steps used in the proof."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("State");
        Formula defect = F.Id("D");
        Formula state = F.Id("x");
        Formula index = F.Id("n");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula defectType = Arrow(stateType, Arrow(nat, real));
        Formula finiteDefect = Call("apply", defect, state, index);
        Formula weight = new Formula.Power(
            D(2), Seq(Minus, Open, index, Plus, D(1), Close));
        Formula normalized = new Formula.Fraction(
            finiteDefect, Seq(D(1), Plus, finiteDefect));
        Formula infiniteDefect = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp,
            weight, Sp, Cdot, Sp, normalized);
        Formula nonnegative = Seq(
            Forall, Sp, Typed(index, nat), Comma, Sp,
            D(0), Sp, Leq, Sp, finiteDefect);
        Formula allZero = Seq(
            Forall, Sp, Typed(index, nat), Comma, Sp,
            finiteDefect, Sp, Eq, Sp, D(0));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(stateType, type), Comma),
            Seq(Grp(), Forall, Sp, Typed(defect, defectType), Comma, Sp,
                Typed(state, stateType), Comma),
            Seq(Grp(), Open, nonnegative, Close, Sp, Rightarrow),
            Seq(Grp(), Open, infiniteDefect, Sp, Eq, Sp, D(0), Close,
                Sp, Leftrightarrow, Sp, Open, allZero, Close, Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
