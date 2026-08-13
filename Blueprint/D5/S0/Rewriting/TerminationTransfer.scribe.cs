using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class TerminationTransferDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman1942 =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Quasi-commuting terminating reductions have a terminating union.",
            H("Termination Transfer for Quasi-Commutation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("termination-of-a-quasi-commuting-union"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/TerminationTransfer.termination_union_of_quasi_commutation"),
                    H("Union termination under quasi-commutation"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp,
                        F.Id("r"), Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp,
                        Lor, Sp, F.Id("s"), Open, F.Id("a"), Comma, Sp, F.Id("b"), Close,
                        Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open, F.Id("r"), Close, Close,
                        Sp, Land, Sp,
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open, F.Id("s"), Close, Close,
                        Sp, Land, Sp,
                        F.Text, Grp(F.Id("s"), Sp, F.Id("quasi-commutes"), Sp,
                            F.Id("ahead"), Sp, F.Id("of"), Sp, F.Id("r")),
                        Sp, Rightarrow, Sp,
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open,
                        F.Text, Grp(F.Id("r"), Sp, F.Id("or"), Sp, F.Id("s")), Close, Close,
                        Dot, Close))),
                    AssessedProvenance.FromLiterature(Newman1942),
                    Blocks(Paragraph(Text(
                        "Nested accessibility induction handles alternating predecessor steps. "
                        + "The quasi-commutation witness moves an r-step ahead of an s-step, "
                        + "while the returned union closure transports accessibility to the endpoint."))),
                    DescribeRole.Theorem))));
}
