using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class DiscountedSensorFusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discounted sensor-fusion distance is the maximum of its component distances.",
        H("Discounted Sensor-Fusion Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-sensor-fusion-distance-is-the-component-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/DiscountedSensorFusion."
                    + "discounted_sensor_fusion_distance_eq_max"),
                H("Discounted sensor-fusion distance is the component maximum"),
                StatementSource.FromAuthor(DiscountedFusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let two sensors observe the same updated state and let each sensor's "
                        + "real-valued discrepancy be nonnegative and uniformly bounded. For a "
                        + "discount factor gamma in (0, 1], define each component distance as "
                        + "the supremum over update times of gamma to that time times the "
                        + "component discrepancy. Define the fused discrepancy pointwise as "
                        + "the maximum of the two component discrepancies.")),
                    Paragraph(Text(
                        "Each discounted component sequence is bounded above by its supplied "
                        + "discrepancy bound. Nonnegativity of every power of gamma lets scalar "
                        + "multiplication distribute across the pointwise maximum. The imported "
                        + "conditionally complete lattice identity ciSup_sup_eq then moves that "
                        + "maximum outside the indexed supremum and gives the equality.")),
                    Paragraph(Text(
                        "Loogle found the exact ciSup_sup_eq and mul_max_of_nonneg declarations, "
                        + "and the proof imports and applies them. LeanSearch returned related "
                        + "supremum declarations but no full-statement match; repository and "
                        + "formalization-record searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula DiscountedDistance(Formula component, Formula y, Formula yPrime) =>
        Seq(
            F.Id("d"), Underscore, Grp(F.Id("gamma")), Caret, Grp(component),
            Open, y, Comma, Sp, yPrime, Close);

    private static Formula DiscountedFusionFormula()
    {
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        return Disp(Seq(
            Forall, Sp, F.Id("gamma"), InMacro, Open, D(0), Comma, Sp, D(1),
            CloseBracket, Comma, Sp,
            Forall, Sp, y, Comma, Sp, yPrime, InMacro, Sp, F.Id("Y"), Comma, Esc,
            DiscountedDistance(D(1, 2), y, yPrime), Sp, Eq, Sp,
            Max, Open,
            DiscountedDistance(D(1), y, yPrime), Comma, Sp,
            DiscountedDistance(D(2), y, yPrime), Close, Dot));
    }
}
