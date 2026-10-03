using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class MeasurableInstrumentHistoryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive finite-dimensional matrix-valued measures admit a common scalar density.",
        H("Measurable Matrix History Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-history-measure"),
                DeclarationHandle.Create(Prefix + "PositiveHistoryMeasure"),
                H("Positive matrix-valued history measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate complex measures form a positive semidefinite matrix "
                        + "on every measurable event. The finite scalar measure is their "
                        + "trace on those events."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-history-density"),
                DeclarationHandle.Create(Prefix + "positive_history_density"),
                H("Common density with a fixed null-set value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Coordinate absolute continuity follows when a positive event "
                            + "matrix has zero trace. Signed Radon-Nikodym derivatives "
                            + "represent its real and imaginary entries on every event.")),
                    Paragraph(Text(
                        "A countable dense family of rational-complex vectors tests "
                            + "positivity simultaneously almost everywhere. Continuity "
                            + "extends the quadratic-form inequalities to all vectors. "
                            + "One measurable null set carries a fixed positive trace-one "
                            + "matrix; coordinate integral uniqueness determines the "
                            + "density almost everywhere."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-history-density-from-coordinates"),
                DeclarationHandle.Create(Prefix + "positive_history_density_from_coordinates"),
                H("The scalar trace measure is derived from the coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real diagonal coordinate measures sum to a nonnegative signed "
                        + "measure, whose finite positive measure has the eventwise matrix "
                        + "trace as its value. The common density and its almost-everywhere "
                        + "uniqueness then apply to these derived coordinates."))),
                DescribeRole.Theorem))));
}
