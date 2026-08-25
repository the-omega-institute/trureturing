using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class WeightedPredictionZeroKernelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel."
            + "weighted_prediction_zero_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive coordinate weights and discount identify zero prediction distance with "
            + "orbit-readout agreement.",
        H("Weighted Prediction Zero Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-prediction-zero-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Zero distance is dynamic indistinguishability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite observation budget J selects equality-valued coordinate "
                        + "readouts. Their static discrepancy is the largest selected "
                        + "positive weight whose two coordinate values differ.")),
                Paragraph(Text(
                    "The dynamic distance is the canonical discounted supremum of that "
                        + "coordinate discrepancy along the two update orbits. Positivity "
                        + "of every selected weight and every discount power makes a zero "
                        + "term equivalent to equality of the corresponding readouts.")),
                Paragraph(Text(
                    "The empty budget is included: its discrepancy is zero and its "
                        + "universal readout-agreement condition is vacuous."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula budget = F.Id("J");
        Formula weights = F.Id("w");
        Formula readouts = F.Id("q");
        Formula update = F.Id("F");
        Formula gamma = F.Id("gamma");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula time = F.Id("n");
        Formula coordinate = F.Id("i");
        Formula positiveWeights = Apply("PositiveWeights", budget, weights);
        Formula discountRange = Seq(D(0), Lt, Sp, gamma, Sp, Leq, Sp, D(1));
        Formula distance = Apply(
            "DiscountedPredictionDistance",
            update, budget, weights, readouts, gamma, first, second);
        Formula firstOrbitReadout = Apply(
            "Readout", readouts, coordinate, Apply("Iterate", update, time, first));
        Formula secondOrbitReadout = Apply(
            "Readout", readouts, coordinate, Apply("Iterate", update, time, second));
        Formula orbitAgreement = Seq(
            Forall, Sp, time, InMacro, Sp, F.Id("N"), Comma, Sp,
            Forall, Sp, coordinate, InMacro, Sp, budget, Comma, Sp,
            firstOrbitReadout, Sp, Eq, Sp, secondOrbitReadout);

        return Disp(Seq(
            positiveWeights, Sp, Land, Sp, discountRange, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, F.Id("X"), Comma,
            RowBreak, Grp(),
            Open, distance, Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
            Open, orbitAgreement, Close, Dot));
    }
}
