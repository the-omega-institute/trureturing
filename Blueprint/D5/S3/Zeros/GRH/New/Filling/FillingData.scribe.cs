using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class FillingDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Filling Data", H("Filling Data"),
        Blocks(
            Paragraph(Text("A polynomial identity that splits a product of determinants (used in New.Rows.Separation). Existence of a Bessel system with tail, Schur and band bounds for the data. Builds the filling record from the global data, with chosen Bessel systems.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/FillingData.columnLevel_zero_eq_comap"),
                H("columnLevel_zero_eq_comap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The level group Data.columnLevel on X₀ is the preimage of the principal congruence subgroup K(g) under the embedding of the finite adelic points of U(X₀) in those of U(Y₀).")))))));
}
