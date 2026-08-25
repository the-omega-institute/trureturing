using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class WeightedObservationQuotientUltrametricDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/MetricGeometryLaws/WeightedObservationQuotientUltrametric."
            + "weighted_observation_zero_kernel_and_quotient_ultrametric";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive weighted equality readouts descend to a genuine observation-quotient "
            + "ultrametric.",
        H("Weighted Observation-Quotient Ultrametric"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-observation-zero-kernel-and-quotient-ultrametric"),
            DeclarationHandle.Create(Declaration),
            H("Zero distance is exactly equality on the observation quotient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite budget J selects a dependent family of readouts. The source "
                        + "distance is the largest selected positive weight at which two "
                        + "readout coordinates differ.")),
                Paragraph(Text(
                    "The quotient is the kernel quotient of the selected joint readout. "
                        + "The displayed computation rule names the canonical lift of the "
                        + "source distance rather than an unspecified existence witness.")),
                Paragraph(Text(
                    "The public clauses give the source zero kernel, the lift computation, "
                        + "nonnegativity, diagonal zero, symmetry, the strong triangle "
                        + "inequality, and identity of indiscernibles on the quotient."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula budget = F.Id("J");
        Formula weights = F.Id("w");
        Formula readouts = F.Id("q");
        Formula coordinate = F.Id("i");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula first = F.Id("u");
        Formula second = F.Id("v");
        Formula third = F.Id("z");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula outputAtCoordinate = Call("Output", output, coordinate);
        Formula readoutType = Grp(
            Forall, Sp, coordinate, Colon, Sp, indexType, Comma, Sp,
            state, Sp, To, Sp, outputAtCoordinate);
        Formula positivity = Seq(
            Forall, Sp, coordinate, InMacro, Sp, budget, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("Weight", weights, coordinate));
        Formula quotient = Call("ObservationQuotient", budget, readouts);

        Formula sourceDistance = Call(
            "WeightedCoordinateDistance", budget, weights, readouts, x, y);
        Formula sourceKernel = Seq(
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, state, Comma, Sp,
            Open, sourceDistance, Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
            Open,
            Call("JointReadout", budget, readouts, x), Sp, Eq, Sp,
            Call("JointReadout", budget, readouts, y),
            Close);

        Formula quotientDistanceOnClasses = Call(
            "WeightedObservationQuotientDistance", budget, weights, readouts,
            Call("QuotientClass", budget, readouts, x),
            Call("QuotientClass", budget, readouts, y));
        Formula computation = Seq(
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, state, Comma, Sp,
            quotientDistanceOnClasses, Sp, Eq, Sp, sourceDistance);

        Formula quotientDistance = Call(
            "WeightedObservationQuotientDistance", budget, weights, readouts,
            first, second);
        Formula quotientDistanceReverse = Call(
            "WeightedObservationQuotientDistance", budget, weights, readouts,
            second, first);
        Formula nonnegative = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, quotient, Comma, Sp,
            D(0), Sp, Leq, Sp, quotientDistance);
        Formula diagonal = Seq(
            Forall, Sp, first, InMacro, Sp, quotient, Comma, Sp,
            Call("WeightedObservationQuotientDistance", budget, weights, readouts,
                first, first),
            Sp, Eq, Sp, D(0));
        Formula symmetry = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, quotient, Comma, Sp,
            quotientDistance, Sp, Eq, Sp, quotientDistanceReverse);
        Formula strongTriangle = Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp, third,
            InMacro, Sp, quotient, Comma, Sp,
            Call("WeightedObservationQuotientDistance", budget, weights, readouts,
                first, third),
            Sp, Leq, Sp,
            Call("max",
                Call("WeightedObservationQuotientDistance", budget, weights, readouts,
                    first, second),
                Call("WeightedObservationQuotientDistance", budget, weights, readouts,
                    second, third)));
        Formula quotientKernel = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, quotient, Comma, Sp,
            Open, quotientDistance, Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
            Open, first, Sp, Eq, Sp, second, Close);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp, state, Colon, Sp, F.Id("Type"), Comma, Sp,
            output, Colon, Sp, indexType, Sp, To, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            budget, Colon, Sp, Call("Finset", indexType), Comma, Sp,
            weights, Colon, Sp, indexType, Sp, To, Sp, real, Comma,
            RowBreak, Grp(),
            readouts, Colon, Sp, readoutType, Comma,
            RowBreak, Grp(),
            Grp(positivity), Sp, Rightarrow,
            RowBreak, Grp(),
            Grp(sourceKernel), Sp, Land,
            RowBreak, Grp(),
            Grp(computation), Sp, Land,
            RowBreak, Grp(),
            Grp(nonnegative), Sp, Land,
            RowBreak, Grp(),
            Grp(diagonal), Sp, Land,
            RowBreak, Grp(),
            Grp(symmetry), Sp, Land,
            RowBreak, Grp(),
            Grp(strongTriangle), Sp, Land,
            RowBreak, Grp(),
            Grp(quotientKernel), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
