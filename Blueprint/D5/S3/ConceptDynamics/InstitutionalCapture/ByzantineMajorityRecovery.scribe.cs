using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class ByzantineMajorityRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict majority recovers a common binary truth when fewer than half the reports are Byzantine.",
        H("Byzantine Majority Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-majority-recovers"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery."
                        + "strict_majority_recovers"),
                H("Strict majority recovers the common truth"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The report population is the finite identity type `Fin n`, each report is "
                            + "binary, and `byzantineCount` counts reports differing from the common "
                            + "honest value `truth`. The bound `byzantineCount reports truth <= f` "
                            + "is the formal reading of at most `f` Byzantine reporters.")),
                    Paragraph(Text(
                        "The threshold `n > 2 * f` makes the matching reports strictly more numerous "
                            + "than the mismatching reports. The named `strictMajority` rule therefore "
                            + "returns `some truth`, including the two possible truth values.")),
                    Paragraph(Text(
                        "The proof uses the pinned finite-filter partition theorem and natural-number "
                            + "arithmetic. A concrete three-report, one-fault-free witness is checked "
                            + "in the Lean module.")),
                    Paragraph(Text(
                        "Repository searches found no accepted Byzantine-majority threshold theorem; "
                            + "the pinned library supplied only the finite cardinal partition used in "
                            + "the proof."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula truth = F.Id("truth");
        Formula reports = F.Id("reports");
        Formula nat = F.Id("Nat");
        Formula boolType = F.Id("Bool");
        Formula fin = Seq(Operatorname, Grp(F.Id("Fin")), Open, n, Close);
        Formula reportType = Arrow(fin, boolType);
        Formula threshold = Seq(n, Sp, Gt, Sp, D(2), Sp, Times, Sp, f);
        Formula bound = Seq(
            Apply("byzantineCount", reports, truth), Sp, Leq, Sp, f);
        Formula result = Seq(
            Apply("strictMajority", reports), Sp, Eq, Sp,
            Seq(Operatorname, Grp(F.Id("some")), Open, truth, Close));

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, f, Colon, Sp, nat, Comma, Sp,
            truth, Colon, Sp, boolType, Comma, Sp,
            reports, Colon, Sp, reportType, Comma, RowBreak, Grp(),
            threshold, Sp, Land, Sp, bound, Sp, Rightarrow, Sp, result, Dot));
    }
}
