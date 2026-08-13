using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class DiagonalSwapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean swap changes every value selected along a self-application diagonal.",
        H("Swap on the Self-Application Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("swap-changes-self-diagonal"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal"),
                H("Swap changes every self-diagonal value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("I"), Comma, Sp,
                    F.Id("P"), Colon, Sp, F.Id("I"), To, Sp, F.Id("I"), To, Sp,
                    Operatorname, Grp(F.Id("Bool")), Comma, Esc,
                    Forall, Sp, F.Id("i"), Colon, F.Id("I"), Comma, Esc,
                    Operatorname, Grp(F.Id("not")), Open,
                    F.Id("P"), Open, F.Id("i"), Comma, F.Id("i"), Close, Close,
                    Sp, Neq, Sp,
                    F.Id("P"), Open, F.Id("i"), Comma, F.Id("i"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two-state swap is instantiated by Boolean negation. For every "
                        + "binary-valued assignment and every index, the theorem selects the "
                        + "self-application value P(i,i) and states that its swap is unequal to "
                        + "that value.")),
                    Paragraph(Text(
                        "The Index quantifier is fully general, including an empty type where the "
                        + "pointwise conclusion is vacuous. The module therefore compiles PUnit as a "
                        + "nonempty index witness and a constant-false PUnit assignment, making the "
                        + "self-application diagonal concrete without weakening the theorem.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. Bool.not_ne_self was an exact "
                        + "hit for the fixed-point-free swap primitive; Bool.not_eq_iff and "
                        + "Bool.not_ne_id were related hits. Repository searches found no existing "
                        + "declaration for the self-diagonal family statement, so the proof is the "
                        + "thin wrapper obtained by applying Bool.not_ne_self to P(i,i).")),
                    Paragraph(Text(
                        "This remains a partial closure of the source theorem. The present declaration "
                        + "proves only the shared swap-on-self-diagonal engine. It does not yet prove "
                        + "the deletion test saying identity loses the mismatch, nor the converse claim "
                        + "that universal diagonal escape forces the minimal Boolean swap. Those two "
                        + "obligations require the stronger hosted declaration before the atom can be "
                        + "treated as fully represented."))),
                DescribeRole.Theorem))));
}
