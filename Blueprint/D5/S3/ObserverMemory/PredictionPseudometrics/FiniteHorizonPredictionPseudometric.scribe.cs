using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionPseudometrics;

internal sealed class FiniteHorizonPredictionPseudometricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prediction distance is a pseudometric whose kernel is finite future agreement.",
        H("Finite-Horizon Prediction Pseudometric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-prediction-pseudometric"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionPseudometrics/"
                        + "FiniteHorizonPredictionPseudometric."
                        + "finite_horizon_prediction_pseudometric"),
                H("Finite prediction distance detects finite future agreement"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonempty state type and a metric output type, take the existing "
                            + "finite prediction distance at unit discount through time T. "
                            + "The output-distance bound is an explicit hypothesis, while the "
                            + "index type Fin(T+1) makes the horizon finite and nonempty.")),
                    Paragraph(Text(
                        "The imported finite-truncation theorem identifies this distance with "
                            + "the maximum of the observer-output distances from time zero "
                            + "through T. The finite product sup metric then supplies zero on "
                            + "the diagonal, symmetry, and the triangle inequality.")),
                    Paragraph(Text(
                        "Distance zero is equivalent to the imported finite-future relation. "
                            + "At infinite horizon, unit-discount prediction distance has zero "
                            + "kernel exactly when the imported complete itineraries agree, "
                            + "which is the relation underlying predictive completion.")),
                    Paragraph(Text(
                        "A checked finite witness changes a hidden coordinate from zero to one "
                            + "hundred while retaining the same constant observer readout. Its raw "
                            + "coordinate distance is one hundred and its prediction distance "
                            + "is zero, separating correlation mass from observer influence."))),
                DescribeRole.Theorem))));

    private static Formula PredictionDistance(Formula horizon, Formula left, Formula right) =>
        Seq(F.Id("D"), Underscore, Grp(horizon), Open, left, Comma, Sp, right, Close);

    private static Formula TheoremFormula()
    {
        Formula horizon = F.Id("T");
        Formula time = F.Id("t");
        Formula left = F.Id("x");
        Formula middle = F.Id("y");
        Formula right = F.Id("z");
        Formula finiteDistance = PredictionDistance(horizon, left, middle);
        Formula readoutDistance = Seq(
            F.Id("d"), Underscore, Grp(F.Id("Z")), Open,
            Pi, Sp, F.Id("U"), Underscore, Grp(time), Sp, left,
            Comma, Sp,
            Pi, Sp, F.Id("U"), Underscore, Grp(time), Sp, middle,
            Close);
        Formula formula = Seq(
            finiteDistance, Sp, Eq, Sp,
            Max, Underscore, Grp(D(0), Sp, Leq, Sp, time, Sp, Leq, Sp, horizon),
            Sp, readoutDistance);
        Formula pseudometric = Seq(
            PredictionDistance(horizon, left, left), Sp, Eq, Sp, D(0), Sp, Land, RowBreak,
            finiteDistance, Sp, Eq, Sp,
            PredictionDistance(horizon, middle, left), Sp, Land, RowBreak,
            finiteDistance, Sp, Leq, Sp,
            PredictionDistance(horizon, left, right), Sp, Plus, Sp,
            PredictionDistance(horizon, right, middle));
        Formula finiteKernel = Seq(
            finiteDistance, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            Forall, Sp, time, Sp, Leq, Sp, horizon, Comma, Sp,
            Pi, Sp, F.Id("U"), Underscore, Grp(time), Sp, left,
            Sp, Eq, Sp,
            Pi, Sp, F.Id("U"), Underscore, Grp(time), Sp, middle);
        Formula infiniteKernel = Seq(
            PredictionDistance(Infty, left, middle), Sp, Eq, Sp, D(0),
            Sp, Leftrightarrow, Sp,
            Call("CompleteItinerary", left), Sp, Eq, Sp,
            Call("CompleteItinerary", middle));
        Formula witness = Seq(
            Exists, Sp, left, Comma, Sp, middle, Comma, Sp,
            Call("RawDistance", left, middle), Sp, Eq, Sp, D(1, 0, 0), Sp, Land, Sp,
            PredictionDistance(horizon, left, middle), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            formula, Sp, Land, RowBreak,
            pseudometric, Sp, Land, RowBreak,
            finiteKernel, Sp, Land, RowBreak,
            infiniteKernel, Sp, Land, RowBreak,
            witness, Dot));
    }
}
