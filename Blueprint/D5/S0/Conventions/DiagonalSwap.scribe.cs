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
                        + "pointwise conclusion is vacuous. The module compiles Bool as a "
                        + "nonempty index witness and a constant-false assignment, making the "
                        + "self-application diagonal concrete without weakening the theorem.")),
                    Paragraph(Text(
                        "The proof computes the swap using the two Boolean constructors in OmegaInit. "
                        + "Transporting the proposition that is true at false and false at true "
                        + "along a hypothetical equality of the two constructors yields a contradiction.")),
                    Paragraph(Text(
                        "This remains a partial closure of the source theorem. The present declaration "
                        + "proves only the shared swap-on-self-diagonal engine. It does not yet prove "
                        + "the deletion test saying identity loses the mismatch, nor the converse claim "
                        + "that universal diagonal escape forces the minimal Boolean swap. Those two "
                        + "obligations require the stronger hosted declaration before the atom can be "
                        + "treated as fully represented."))),
                DescribeRole.Theorem))));
}
