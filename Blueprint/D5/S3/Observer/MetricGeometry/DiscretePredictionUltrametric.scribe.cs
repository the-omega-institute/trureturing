using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class DiscretePredictionUltrametricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete-output prediction distance satisfies the strong triangle inequality.",
        H("Discrete Prediction Ultrametric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discrete-prediction-distance-strong-triangle"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric."
                    + "discounted_prediction_distance_strong_triangle"),
                H("Discrete prediction distance obeys the strong triangle inequality"),
                StatementSource.FromAuthor(StrongTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a deterministic update and a readout into a discrete output type. "
                        + "The output discrepancy is zero when two outputs agree and one "
                        + "otherwise. For a discount factor gamma in (0, 1], the prediction "
                        + "distance is the supremum over update times of the discounted output "
                        + "discrepancy.")),
                    Paragraph(Text(
                        "The discrete discrepancy obeys the strong triangle inequality at each "
                        + "time. Nonnegative discount powers preserve that inequality. "
                        + "Boundedness by one supplies the conditionally complete suprema, and "
                        + "moving the pointwise maximum through the supremum proves the displayed "
                        + "law.")),
                    Paragraph(Text(
                        "Loogle found the exact ciSup_sup_eq and mul_max_of_nonneg declarations "
                        + "used in the proof. LeanSearch returned the generic ultrametric "
                        + "interfaces and a fixed half-discount sequence metric, but no theorem "
                        + "for this arbitrary-discount observer distance. Repository and "
                        + "formalization-record searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula PredictionDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(GammaLower), Open, left, Comma, Sp, right, Close);

    private static Formula StrongTriangleFormula()
    {
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, GammaLower, InMacro, Open, D(0), Comma, Sp, D(1),
            CloseBracket, Comma, Sp,
            Forall, Sp, y, Comma, Sp, yPrime, Comma, Sp, z,
            InMacro, Sp, F.Id("Y"), Comma, Esc,
            PredictionDistance(y, z), Sp, Leq, Sp,
            Max, Open,
            PredictionDistance(y, yPrime), Comma, Sp,
            PredictionDistance(yPrime, z), Close, Dot));
    }
}
