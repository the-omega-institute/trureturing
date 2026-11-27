using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class GreenbergWilesBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Greenberg Wiles Bound", H("Greenberg Wiles Bound"),
        Blocks(
            Paragraph(Text("Bound on trivialised cocycles when a central element acts without fixed vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/GreenbergWilesBound.hasFewCocycles_of_central"),
                H("hasFewCocycles_of_central"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let K be totally complex, s auxiliary primes for l^r (r ≠ 0), N and U (SplitPlaces), indexed by ι, with Frobenii φ_i; V finite, l^r-torsion, U-fixed; z central modulo U, fixing l-power roots of unity, z − 1 onto V. If U fixes each l^r-th root, fixed by all φ_i, of a U-fixed N-unit, the trivialised cocycles unramified outside N and s are finite in number, at most (#V)^{#ι+1}.")))))));
}
