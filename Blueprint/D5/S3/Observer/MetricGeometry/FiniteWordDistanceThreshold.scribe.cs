using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class FiniteWordDistanceThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite readout agreement is exactly a discrete prediction-distance threshold.",
        H("Finite Word Distance Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-word-equivalence-is-a-prediction-distance-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/FiniteWordDistanceThreshold."
                    + "finite_word_equivalent_iff_prediction_distance_le"),
                H("Finite words are exactly discrete prediction balls"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an update, a discrete readout, and a discount factor gamma strictly "
                            + "between zero and one. For every natural depth m and pair of states, "
                            + "agreement of the readouts at times zero through m is equivalent to "
                            + "their discounted prediction distance being at most gamma to the "
                            + "power m plus one.")),
                    Paragraph(Text(
                        "The forward direction specializes the finite-readout fiber diameter "
                            + "bound to the zero-one output discrepancy. Conversely, a mismatch "
                            + "at time k at most m contributes gamma to the power k to the "
                            + "supremum. Strict geometric decay makes that contribution larger "
                            + "than gamma to the power m plus one, contradicting the threshold.")),
                    Paragraph(Text(
                        "Loogle found no declaration named for this prediction distance, and the "
                            + "full-shape LeanSearch query returned only unrelated finite-product "
                            + "supremum metrics. Both searches identified the exact geometric "
                            + "decay result pow_lt_pow_right_of_lt_one₀. The proof also applies "
                            + "le_ciSup and the repository finite-word fiber diameter theorem; "
                            + "repository and formalization searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula ReadoutAt(Formula state, Formula time) =>
        Seq(F.Id("q"), Open, Tau, Caret, Grp(time), Open, state, Close, Close);

    private static Formula PredictionDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(GammaLower), Open, left, Comma, Sp, right, Close);

    private static Formula ThresholdFormula()
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        return Disp(Seq(
            Forall, Sp, GammaLower, InMacro, Sp, Open, D(0), Comma, Sp, D(1), Close,
            Comma, Esc,
            Forall, Sp, m, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, y, Comma, Sp, yPrime, InMacro, Sp, F.Id("Y"), Comma, Esc,
            Open, Forall, Sp, k, Sp, Leq, Sp, m, Comma, Esc,
            ReadoutAt(y, k), Eq, ReadoutAt(yPrime, k), Close,
            Sp, Leftrightarrow, Sp,
            PredictionDistance(y, yPrime), Sp, Leq, Sp,
            GammaLower, Caret, Grp(m, Plus, D(1)), Dot));
    }
}
