using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class BellmanMaxEquationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discounted prediction distance satisfies its one-step Bellman maximum equation.",
        H("Bellman Maximum Equation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-prediction-distance-bellman-equation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BellmanMaxEquation."
                    + "discounted_prediction_distance_bellman"),
                H("Discounted prediction distance obeys the Bellman maximum equation"),
                StatementSource.FromAuthor(BellmanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an update, a readout, and a nonnegative real discrepancy bounded "
                        + "by D. For a discount factor gamma in (0, 1], the discounted "
                        + "prediction distance is the supremum over update times of gamma to "
                        + "that time times the observed discrepancy.")),
                    Paragraph(Text(
                        "The time-zero term gives the current discrepancy. Every positive-time "
                        + "term factors as gamma times the corresponding term after one update. "
                        + "Boundedness supplies the conditionally complete suprema, and the two "
                        + "families give the displayed maximum.")),
                    Paragraph(Text(
                        "Loogle found the exact Real.mul_iSup_of_nonneg declaration used to "
                        + "move gamma through the shifted supremum. Its complete-lattice "
                        + "sup_iSup_nat_succ result does not apply to Real. LeanSearch returned "
                        + "nearby supremum and fixed-point results but no full-statement match; "
                        + "repository and formalization-record searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula Distance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(F.Id("O")), Open, left, Comma, Sp, right, Close);

    private static Formula PredictionDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(GammaLower), Open, left, Comma, Sp, right, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula BellmanFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula distanceBound = Seq(
            Forall, Sp, a, Comma, Sp, b, InMacro, Sp, F.Id("O"), Comma, Esc,
            D(0), Leq, Sp, Distance(a, b), Leq, Sp, F.Id("D"));
        return Disp(Seq(
            Forall, Sp, GammaLower, InMacro, Open, D(0), Comma, Sp, D(1),
            CloseBracket, Comma, Sp,
            distanceBound, Sp, Rightarrow, Sp,
            Forall, Sp, y, Comma, Sp, yPrime, InMacro, Sp, F.Id("Y"), Comma, Esc,
            PredictionDistance(y, yPrime), Sp, Eq, Sp,
            Max, Open,
            Distance(Apply(F.Id("q"), y), Apply(F.Id("q"), yPrime)),
            Comma, Sp, GammaLower, Sp, PredictionDistance(
                Apply(Tau, y), Apply(Tau, yPrime)),
            Close, Dot));
    }
}
