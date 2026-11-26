using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class VisibleTwoStepDefectDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/VisibleTwoStepDefect.";
    private static readonly Formula P = F.Id("P"), T = F.Id("T"), V = F.Id("V"), X = F.Id("v");
    private static readonly Formula Form = Seq(F.Id("d"), Open, X, Close);
    private static readonly Formula AllVisible = Seq(Forall, Sp, X, InMacro, Sp, V, Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The defect between two full steps and two successively projected steps detects when a symmetric time operator leaves the visible subspace invariant.",
        H("Visible two-step compression defect"),
        Blocks(
            Describe.Lean(DescribeId.Create("defect-form"), DeclarationHandle.Create(Module + "defectForm"),
                H("The quadratic defect on a visible vector"),
                StatementSource.FromAuthor(Disp(Seq(Form, Eq, Langle, Sp, X, Comma, Open, P, T, Caret, D(2),
                    Minus, P, T, P, T, Close, X, Rangle))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let V be a subspace of a real inner-product space that admits the orthogonal projection P. On v in V, compare the final projections after two bounded linear steps T, with and without a projection between the steps."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("vanishing"), DeclarationHandle.Create(Module + "visible_two_step_defect"),
                H("Squared leakage and invariance"),
                StatementSource.FromAuthor(Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, AllVisible,
                    Form, Eq, Vert, Open, D(1), Minus, P, Close, T, X, Vert, Caret, D(2),
                    RowBreak, Amp, Open, AllVisible, Form, Eq, D(0), Close, Sp, Leftrightarrow, Sp,
                    Open, AllVisible, T, X, InMacro, Sp, V, Close, End, Grp(F.Id("aligned"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Suppose T is symmetric. Move the outer projection across the inner product, where it fixes v, and then move one copy of T. Orthogonality removes the projection of Tv against its residual. The remaining inner product is the squared residual norm, which vanishes exactly when Tv belongs to V."))), DescribeRole.Theorem))));
}
