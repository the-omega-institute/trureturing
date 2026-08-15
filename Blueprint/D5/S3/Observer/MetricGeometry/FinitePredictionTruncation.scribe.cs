using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class FinitePredictionTruncationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Bellman prediction distances have an exact maximum formula and geometric error.",
        H("Finite Prediction Truncation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-bellman-prediction-formula-and-error"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/FinitePredictionTruncation."
                    + "finite_prediction_truncation_formula_and_error"),
                H("Finite prediction truncation has a geometric error bound"),
                StatementSource.FromAuthor(TruncationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Start the finite prediction distance at zero and apply the Bellman "
                            + "maximum operator m plus one times. Assume the output discrepancy "
                            + "is nonnegative and bounded by D, and gamma lies in (0, 1]. The "
                            + "iterate is the maximum of the discounted discrepancies at times "
                            + "zero through m.")),
                    Paragraph(Text(
                        "Induction splits the finite maximum into its time-zero term and its "
                            + "discounted tail. Comparing the same split with the infinite "
                            + "Bellman equation shows that the finite iterate is below the full "
                            + "distance. The imported max-subtraction bound contracts the "
                            + "remaining error by gamma at each step.")),
                    Paragraph(Text(
                        "Loogle returned named finite-supremum support declarations. LeanSearch "
                            + "returned related finite-supremum and geometric truncation results "
                            + "but no full theorem match. After type inspection, the Lean proof "
                            + "imports and applies max_sub_max_le_max and the conditionally "
                            + "complete finite-supremum library lemmas; "
                            + "repository and formalization searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula ReadoutAt(Formula state, Formula time) =>
        Seq(F.Id("q"), Open, Tau, Caret, Grp(time), Open, state, Close, Close);

    private static Formula OutputDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(F.Id("O")), Open, left, Comma, Sp, right, Close);

    private static Formula PredictionDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(GammaLower), Open, left, Comma, Sp, right, Close);

    private static Formula FiniteDistance(Formula left, Formula right, Formula depth) =>
        Seq(F.Id("p"), Underscore, Grp(depth), Open, left, Comma, Sp, right, Close);

    private static Formula TruncationFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula depth = Seq(m, Plus, D(1));
        Formula finiteDistance = FiniteDistance(y, yPrime, depth);
        return Disp(Seq(
            Forall, Sp, GammaLower, InMacro, Open, D(0), Comma, Sp, D(1),
            CloseBracket, Comma, Sp,
            Open, Forall, Sp, a, Comma, Sp, b, InMacro, Sp, F.Id("O"), Comma, Esc,
            D(0), Leq, Sp, OutputDistance(a, b), Leq, Sp, F.Id("D"), Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, m, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, y, Comma, Sp, yPrime, InMacro, Sp, F.Id("Y"), Comma, Esc,
            finiteDistance, Sp, Eq, Sp,
            Max, Underscore, Grp(D(0), Sp, Leq, Sp, k, Sp, Leq, Sp, m), Sp,
            GammaLower, Caret, Grp(k), Sp,
            OutputDistance(ReadoutAt(y, k), ReadoutAt(yPrime, k)), Comma, Esc,
            D(0), Leq, Sp,
            PredictionDistance(y, yPrime), Minus, finiteDistance,
            Sp, Leq, Sp, GammaLower, Caret, Grp(depth), Sp, F.Id("D"), Dot));
    }
}
