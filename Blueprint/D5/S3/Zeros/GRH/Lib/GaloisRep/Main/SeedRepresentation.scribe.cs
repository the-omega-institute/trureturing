using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class SeedRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seed Representation", H("Seed Representation"),
        Blocks(
            Paragraph(Text("Galois representation from geometry for odd-rank forms of cuspidal type and free weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SeedRepresentation.exists_rep_of_cuspidal_type"),
                H("exists_rep_of_cuspidal_type"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let E ⊃ ℚ(√−d) be stably unramified, f of odd rank with polynomials P off S, of cuspidal type at w₀ ∈ S above ℓ, with free jumps at v ∉ S ∪ S̄ over w₀'s split prime u; let w' lie over a split prime, u if w' ∣ ℓ. Some continuous r has characteristic polynomial ιP_w at most Frobenii, and SphericalClause at w' if w', w̄' ∉ S.")))))));
}
