using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.LedgerGovernance;

internal sealed class TerminalLedgerPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal grades partition the semantic ledger into migrated, wall, and resident sets.",
        H("Terminal Ledger Partition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-ledger-three-way-partition"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/LedgerGovernance/TerminalLedgerPartition."
                        + "terminal_ledger_three_way_partition"),
                H("Terminal grades give a three-way ledger partition"),
                StatementSource.FromAuthor(PartitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a countable statement ledger take values in a finite partially "
                            + "ordered grade space, and assume every post-enrollment grade track "
                            + "has finitely many revisions. The pointwise ledger-limit theorem "
                            + "therefore supplies a unique terminal grading.")),
                    Paragraph(Text(
                        "Let Sem be the terminal semantic domain and W a wall contained in Sem. "
                            + "Every gatekeeper remains positive, joint positivity of a wall "
                            + "statement and all gatekeepers is forbidden, and consistency rules "
                            + "out forbidden wall configurations.")),
                    Paragraph(Text(
                        "The migrated set M consists exactly of semantic statements with a "
                            + "positive terminal grade. The resident set R is Sem with M and W "
                            + "removed. The imported terminal-grade decomposition theorem gives "
                            + "the displayed cover equality and all three pairwise disjointness "
                            + "claims directly."))),
                DescribeRole.Theorem)),
        []));

    private static Formula GradeAt(Formula time, Formula statement) =>
        Seq(SigmaLower, Underscore, Grp(time), Open, statement, Close);

    private static Formula Positive(Formula time, Formula statement) =>
        Seq(GradeAt(time, statement), Sp, InMacro, Sp, F.Id("Gplus"));

    private static Formula Forbidden(Formula time, Formula statement) =>
        Seq(Operatorname, Grp(F.Id("forbidden")), Open, time, Comma, statement, Close);

    private static Formula PartitionFormula()
    {
        Formula time = F.Id("t"), statement = F.Id("s"), wallStatement = F.Id("w");
        Formula gatekeeper = F.Id("g"), cutoff = F.Id("N");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("Countable")), Open, F.Id("Statement"), Close,
            Comma, Sp,
            Operatorname, Grp(F.Id("Finite")), Open, F.Id("Grade"), Close,
            Comma, Sp,
            Operatorname, Grp(F.Id("PartialOrder")), Open, F.Id("Grade"), Close,
            Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("FiniteRevisions")), Open, F.Id("history"), Close,
            Comma, Sp, F.Id("W"), Sp, Subseteq, Sp, F.Id("Sem"), Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, gatekeeper, Sp, InMacro, Sp, F.Id("T"),
            Comma, Sp, Positive(time, gatekeeper), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"),
            Comma, Sp, Positive(time, wallStatement), Sp, Land, Sp,
            Forall, Sp, gatekeeper, Sp, InMacro, Sp, F.Id("T"), Comma, Sp,
            Positive(time, gatekeeper), Sp, Rightarrow, Sp,
            Forbidden(time, wallStatement), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"),
            Comma, Sp, Neg, Sp, Forbidden(time, wallStatement), Close, RowBreak, Grp(),
            Rightarrow, Sp, Exists, Bang, Sp,
            SigmaLower, Underscore, Grp(Infty), Colon, Sp,
            F.Id("Statement"), Sp, To, Sp, F.Id("Grade"), Comma, RowBreak, Grp(),
            Open, Forall, Sp, statement, Comma, Sp, Exists, Sp, cutoff, Sp, Geq, Sp,
            Operatorname, Grp(F.Id("enrolledAt")), Open, statement, Close, Comma, Sp,
            Forall, Sp, time, Sp, Geq, Sp, cutoff, Comma, Sp,
            GradeAt(time, statement), Sp, Eq, Sp,
            SigmaLower, Underscore, Grp(Infty), Open, statement, Close, Close,
            Sp, Land, RowBreak, Grp(),
            F.Id("M"), Sp, Eq, Sp,
            Operatorname, Grp(F.Id("intersection")), Open,
            F.Id("Sem"), Comma,
            Operatorname, Grp(F.Id("preimage")), Open,
            SigmaLower, Underscore, Grp(Infty), Comma, F.Id("Gplus"), Close, Close,
            Comma, Sp,
            F.Id("R"), Sp, Eq, Sp, F.Id("Sem"), Sp, Setminus, Sp,
            Open, F.Id("M"), Sp, Operatorname, Grp(F.Id("union")), Sp, F.Id("W"), Close,
            Comma, RowBreak, Grp(),
            F.Id("Sem"), Sp, Eq, Sp, F.Id("M"), Sp,
            Operatorname, Grp(F.Id("union")), Sp, F.Id("W"), Sp,
            Operatorname, Grp(F.Id("union")), Sp, F.Id("R"), Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("M"), Comma, F.Id("W"), Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("M"), Comma, F.Id("R"), Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Disjoint")), Open, F.Id("W"), Comma, F.Id("R"), Close,
            Dot, End, Grp(F.Id("gathered"))));
    }
}
