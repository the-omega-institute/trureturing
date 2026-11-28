using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class LabelledColumnsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labelled Columns", H("Labelled Columns"),
        Blocks(
            Paragraph(Text("Labelled representations are rows via tame inertia; quadratic inertia relation at twist primes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/LabelledColumns.isLabelledColumn_of_hasProductLabel"),
                H("isLabelledColumn_of_hasProductLabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The representation attached to an eigenform of rank m, spherical at the places off S or above ℓg that are neither chosen nor conjugate to a chosen place, and with label c_i (HasProductLabel) at each chosen place, is a labelled column with labels c_i·(X − 1)^{m−r}.")))))));
}
