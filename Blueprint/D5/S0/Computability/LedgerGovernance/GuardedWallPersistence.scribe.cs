using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.LedgerGovernance;

internal sealed class GuardedWallPersistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A guarded wall stays outside positive grades at every time and in the unique ledger limit.",
        H("Guarded Wall Persistence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guarded-wall-persists-in-ledger-limit"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/LedgerGovernance/GuardedWallPersistence."
                        + "guarded_wall_persists_in_ledger_limit"),
                H("A guarded wall persists in the ledger limit"),
                StatementSource.FromAuthor(GuardedWallFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a countable ledger take values in a finite partially ordered grade "
                            + "space, and assume every post-enrollment grade track has only "
                            + "finitely many revisions. Let W be the guarded wall, T its "
                            + "gatekeepers, and Gplus the positive grades.")),
                    Paragraph(Text(
                        "Every gatekeeper remains positive. Joint positivity of a wall statement "
                            + "and all gatekeepers is declared forbidden, while consistency rules "
                            + "out every such forbidden configuration. The existing guarded-wall "
                            + "theorem therefore excludes W from Gplus at every finite time.")),
                    Paragraph(Text(
                        "The existing ledger-limit theorem supplies the unique terminal grading. "
                            + "Evaluating finite-time wall exclusion at each statement's stability "
                            + "cutoff proves that every wall statement remains outside Gplus in "
                            + "that terminal grading."))),
                DescribeRole.Theorem)),
        []));

    private static Formula GradeAt(Formula time, Formula statement) =>
        Seq(SigmaLower, Underscore, Grp(time), Open, statement, Close);

    private static Formula Positive(Formula time, Formula statement) =>
        Seq(GradeAt(time, statement), Sp, InMacro, Sp, F.Id("Gplus"));

    private static Formula Forbidden(Formula time, Formula statement) =>
        Seq(Operatorname, Grp(F.Id("forbidden")), Open, time, Comma, statement, Close);

    private static Formula GuardedWallFormula()
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
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, gatekeeper, Sp, InMacro, Sp, F.Id("T"),
            Comma, Sp, Positive(time, gatekeeper), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"),
            Comma, Sp, Positive(time, wallStatement), Sp, Land, Sp,
            Forall, Sp, gatekeeper, Sp, InMacro, Sp, F.Id("T"), Comma, Sp,
            Positive(time, gatekeeper), Sp, Rightarrow, Sp,
            Forbidden(time, wallStatement), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"),
            Comma, Sp, Neg, Sp, Forbidden(time, wallStatement), Close, RowBreak, Grp(),
            Rightarrow, Sp,
            Open, Forall, Sp, time, Comma, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"),
            Comma, Sp, Neg, Sp, Open, Positive(time, wallStatement), Close, Close,
            Sp, Land, RowBreak, Grp(),
            Exists, Bang, Sp, SigmaLower, Underscore, Grp(Infty), Colon, Sp,
            F.Id("Statement"), Sp, To, Sp, F.Id("Grade"), Comma, RowBreak, Grp(),
            Open, Forall, Sp, statement, Comma, Sp, Exists, Sp, cutoff, Sp, Geq, Sp,
            Operatorname, Grp(F.Id("enrolledAt")), Open, statement, Close, Comma, Sp,
            Forall, Sp, time, Sp, Geq, Sp, cutoff, Comma, Sp,
            GradeAt(time, statement), Sp, Eq, Sp,
            SigmaLower, Underscore, Grp(Infty), Open, statement, Close, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, wallStatement, Sp, InMacro, Sp, F.Id("W"), Comma, Sp,
            Neg, Sp, Open,
            SigmaLower, Underscore, Grp(Infty), Open, wallStatement, Close,
            Sp, InMacro, Sp, F.Id("Gplus"), Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
