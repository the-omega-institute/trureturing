using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class TwoTruthReportVectorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InstitutionalCapture/TwoTruthReportVector."
            + "two_truth_report_vector_exists";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the half-honest boundary, one report vector is admissible for both Boolean truths.",
        H("Two-Truth Report Vector"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-truth-report-vector-exists"),
            DeclarationHandle.Create(Declaration),
            H("One report vector supports two allowed truth worlds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Reports form a Boolean vector indexed by Fin n, and byzantineCount "
                        + "counts entries that disagree with a proposed common truth.")),
                Paragraph(Text(
                    "When n is at most f, the constant-false vector meets both bounds. "
                        + "Otherwise the vector is true on the first f indices and false "
                        + "elsewhere. Its two disagreement counts are f and n minus f, "
                        + "and the threshold bounds both by f. Subsets of the reporters "
                        + "agreeing with each truth give disjoint groups H0 and H1, each "
                        + "with exactly n minus f members."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula reports = F.Id("reports");
        Formula reporter = F.Id("reporter");
        Formula H0 = F.Id("H0");
        Formula H1 = F.Id("H1");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula reportVector = Arrow(Call("Fin", n), boolType);
        Formula reporterSet = Call("Finset", Call("Fin", n));
        Formula threshold = Seq(n, Sp, Leq, Sp, D(2), Sp, Times, Sp, f);
        Formula H0ReportsFalse = Seq(
            Forall, Sp, reporter, Sp, InMacro, Sp, H0, Comma, Sp,
            reports, Open, reporter, Close, Sp, Eq, Sp, F.Id("false"));
        Formula H1ReportsTrue = Seq(
            Forall, Sp, reporter, Sp, InMacro, Sp, H1, Comma, Sp,
            reports, Open, reporter, Close, Sp, Eq, Sp, F.Id("true"));
        Formula falseBound = Seq(
            Call("byzantineCount", reports, F.Id("false")), Sp, Leq, Sp, f);
        Formula trueBound = Seq(
            Call("byzantineCount", reports, F.Id("true")), Sp, Leq, Sp, f);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Comma, Sp, f, Sp, InMacro, Sp, naturals, Comma),
            Seq(threshold, Sp, Rightarrow, Sp,
                Exists, Sp, H0, Comma, Sp, H1, Colon, Sp, reporterSet, Comma),
            Seq(Call("Disjoint", H0, H1), Sp, Land, Sp,
                Call("card", H0), Sp, Eq, Sp, n, Sp, Minus, Sp, f, Sp, Land, Sp,
                Call("card", H1), Sp, Eq, Sp, n, Sp, Minus, Sp, f, Sp, Land),
            Seq(Exists, Sp, reports, Colon, Sp, reportVector, Comma, Sp,
                Grp(H0ReportsFalse), Sp, Land, Sp, Grp(H1ReportsTrue), Sp, Land),
            Seq(falseBound, Sp, Land, Sp, trueBound, Dot),
        ]));
    }
}
