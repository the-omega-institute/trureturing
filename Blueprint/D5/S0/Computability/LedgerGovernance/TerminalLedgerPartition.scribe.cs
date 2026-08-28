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

    private static Formula Forbidden(Formula time, Formula statement) =>
        Seq(Operatorname, Grp(F.Id("forbidden")), Open, time, Comma, statement, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula CallHistory(string field, Formula history, params Formula[] arguments) =>
        Call(field, [history, .. arguments]);

    private static Formula PartitionFormula()
    {
        Formula statementType = F.Id("Statement"), gradeType = F.Id("Grade");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula history = SigmaLower;
        Formula positiveGrades = F.Id("Gplus"), semantic = F.Id("Sem");
        Formula wall = F.Id("W"), gatekeepers = F.Id("T");
        Formula time = F.Id("t"), statement = F.Id("s"), wallStatement = F.Id("w");
        Formula gatekeeper = F.Id("g"), cutoff = F.Id("N");
        Formula historyGradeAt(Formula t, Formula s) => CallHistory("grade", history, s, t);
        Formula enrolledAt(Formula s) => CallHistory("enrolledAt", history, s);
        Formula revisionTrack = Seq(Open, time, Colon, Sp, naturals, Sp, Mapsto, Sp,
            historyGradeAt(time, statement), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, statementType, Comma, Sp, gradeType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Typeclass("Countable", statementType), Comma, Sp,
            Typeclass("Finite", gradeType), Comma, Sp,
            Typeclass("PartialOrder", gradeType), Comma, RowBreak, Grp(),
            Forall, Sp, history, Colon, Sp,
            Call("LedgerHistory", statementType, gradeType), Comma, RowBreak, Grp(),
            Open, Forall, Sp, statement, Colon, Sp, statementType, Comma, Sp,
            Call("Finite", Call("revisionTimesFrom", enrolledAt(statement), revisionTrack)),
            Close, Comma, RowBreak, Grp(),
            Forall, Sp, positiveGrades, Colon, Sp, Call("Set", gradeType), Comma, Sp,
            Forall, Sp, semantic, Comma, Sp, wall, Comma, Sp, gatekeepers, Colon, Sp,
            Call("Set", statementType), Comma, RowBreak, Grp(),
            wall, Sp, Subseteq, Sp, semantic, Comma, Sp,
            Forall, Sp, F.Id("forbidden"), Colon, Sp,
            naturals, Sp, To, Sp, statementType, Sp, To, Sp, proposition,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Colon, Sp, naturals, Comma, Sp,
            gatekeeper, Colon, Sp, statementType, Comma, Sp,
            gatekeeper, Sp, InMacro, Sp, gatekeepers, Sp, Rightarrow, Sp,
            historyGradeAt(time, gatekeeper), Sp, InMacro, Sp, positiveGrades,
            Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Colon, Sp, naturals, Comma, Sp,
            wallStatement, Colon, Sp, statementType, Comma, Sp,
            wallStatement, Sp, InMacro, Sp, wall, Sp, Rightarrow, Sp,
            historyGradeAt(time, wallStatement), Sp, InMacro, Sp, positiveGrades,
            Sp, Rightarrow, Sp,
            Open, Forall, Sp, gatekeeper, Colon, Sp, statementType, Comma, Sp,
            gatekeeper, Sp, InMacro, Sp, gatekeepers, Sp, Rightarrow, Sp,
            historyGradeAt(time, gatekeeper), Sp, InMacro, Sp, positiveGrades, Close,
            Sp, Rightarrow, Sp,
            Forbidden(time, wallStatement), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Colon, Sp, naturals, Comma, Sp,
            wallStatement, Colon, Sp, statementType, Comma, Sp,
            wallStatement, Sp, InMacro, Sp, wall, Sp, Rightarrow, Sp,
            Neg, Sp, Forbidden(time, wallStatement), Close, RowBreak, Grp(),
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
