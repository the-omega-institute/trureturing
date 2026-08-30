using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class GoldenLocalBranchClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mod-five quadratic character controls a two-branch complex local operator.",
        H("Golden Local Branch Classification"),
        Blocks(
            DefinitionNode(
                "even-branch-projection",
                "evenBranchProjection",
                "Even branch projection",
                "The half-sum of the identity and the canonical bit flip projects to the fixed branch."),
            DefinitionNode(
                "odd-branch-projection",
                "oddBranchProjection",
                "Odd branch projection",
                "The half-difference of the identity and the canonical bit flip projects to the negated branch."),
            DefinitionNode(
                "golden-local-branch-operator",
                "goldenLocalBranchOperator",
                "Golden local branch operator",
                "The even projector is combined with the odd projector weighted by the Legendre "
                    + "character modulo five."),
            Describe.Lean(
                DescribeId.Create("golden-local-branch-classification"),
                Handle("golden_local_branch_classification"),
                H("The local operator ramifies only at five"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The determinant is the mod-five quadratic character. Character one gives "
                            + "the identity, character minus one gives the canonical bit flip, and character "
                            + "zero fixes the even vector while killing the odd vector. For prime "
                            + "indices, noninvertibility is equivalent to the index being five. The "
                            + "same statement includes the ramified-square identity on GoldenInt.")),
                    Paragraph(Text(
                        "The proof uses Mathlib's two-by-two determinant and matrix invertibility "
                            + "criteria, the Legendre zero criterion, and the frozen canonical "
                            + "golden-integer square theorem."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);

    private static Formula ClassificationFormula()
    {
        Formula prime = F.Id("p");
        Formula character = Call("legendreSym", D(5), prime);
        Formula localOperator = Call("goldenLocalBranchOperator", prime);
        Formula oddVector = Call("vec2", D(1), Seq(Minus, D(1)));
        Formula evenVector = Call("vec2", D(1), D(1));
        Formula ramifiedSquare = new Formula.Power(
            Seq(Open, Minus, D(1), Sp, Plus, Sp, D(2), Varphi, Close),
            D(2));

        return Disp(Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Open, Call("Prime", prime), Sp, Rightarrow, Sp,
            Call("det", localOperator), Sp, Eq, Sp, character, Close, Sp, Land, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Rightarrow, Sp,
            Open, character, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp, Open,
            Call("det", localOperator), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            localOperator, Sp, Eq, Sp, F.Id("I"), Close, Close, Close, Sp, Land, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Rightarrow, Sp,
            Open, character, Sp, Eq, Sp, Minus, D(1), Sp, Rightarrow, Sp, Open,
            Call("det", localOperator), Sp, Eq, Sp, Minus, D(1), Sp, Land, Sp,
            localOperator, Sp, Eq, Sp, F.Id("bitFlip"), Close, Close, Close, Sp, Land, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Rightarrow, Sp,
            Open, character, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp, Open,
            Call("det", localOperator), Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            localOperator, Sp, Eq, Sp, F.Id("evenBranchProjection"), Sp, Land, RowBreak, Grp(),
            Call("mulVec", localOperator, oddVector), Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Call("mulVec", localOperator, evenVector), Sp, Eq, Sp, evenVector,
            Close, Close, Close, Sp, Land, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Rightarrow, Sp,
            Open, Neg, Call("IsUnit", localOperator), Sp, Leftrightarrow, Sp,
            prime, Sp, Eq, Sp, D(5), Close, Close, Sp, Land, RowBreak, Grp(),
            Call("cast", D(5), F.Id("GoldenInt")), Sp, Eq, Sp, ramifiedSquare, Dot));
    }
}
