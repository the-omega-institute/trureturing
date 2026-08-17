using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class GroupValuedDiagonalEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A free group action shifts diagonal coordinates and forces pointwise escape.",
        H("Group-Valued Diagonal Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("group-valued-diagonal-escape"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/GroupValuedDiagonalEscape."
                        + "group_valued_diagonal_escape"),
                H("Group-valued diagonal escape"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, Esc,
                    Operatorname, Grp(F.Id("orbit")), Open,
                    F.Id("h"), Sp, Cdot, Sp,
                    F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close,
                    Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("orbit")), Open,
                    F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close, Close,
                    Sp, Land, Sp,
                    Forall, Sp, F.Id("a"), Comma, Esc,
                    Operatorname, Grp(F.Id("coord")), Open,
                    F.Id("h"), Sp, Cdot, Sp,
                    F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close,
                    Close, Sp, Eq, Sp, F.Id("h"), Thin,
                    Operatorname, Grp(F.Id("coord")), Open,
                    F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close, Close,
                    Sp, Land, Sp, Open, F.Id("h"), Sp, Neq, Sp, D(1), Sp,
                    Rightarrow, Sp, Forall, Sp, F.Id("a"), Comma, Esc,
                    F.Id("h"), Sp, Cdot, Sp,
                    F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close,
                    Sp, Neq, Sp, F.Id("E"), Open, F.Id("a"), Comma, F.Id("a"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose one representative in every orbit of a free left group action. "
                            + "The resulting normal-form coordinate writes each point uniquely as "
                            + "a group element acting on its chosen orbit representative.")),
                    Paragraph(Text(
                        "Left translation by h does not change the orbit projection and multiplies "
                            + "the normal-form group coordinate on the left by h. If h is not the "
                            + "identity, freeness excludes equality with the original diagonal value "
                            + "at every address.")),
                    Paragraph(Text(
                        "The pinned Mathlib declaration "
                            + "MulAction.selfEquivOrbitsQuotientProd' supplies the free-action "
                            + "normal form directly. IsCancelSMul.eq_one_of_smul supplies the exact "
                            + "final escape step. The formal theorem is more general than the finite "
                            + "group setting because neither conclusion uses finiteness."))),
                DescribeRole.Theorem))));
}
