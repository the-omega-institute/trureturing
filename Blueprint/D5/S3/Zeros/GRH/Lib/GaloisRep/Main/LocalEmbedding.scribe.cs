using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class LocalEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Embedding", H("Local Embedding"),
        Blocks(
            Paragraph(Text("Local conditions: unramified or crystalline, finite type, killing polynomials, jumps. Decomposition group versus local Galois group: Frobenius, inertia, cyclotomic character agree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding.isFrob_iff"),
                H("isFrob_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s in the decomposition group of A and j = h.toGp, the map to Gal(ℚ̄_ℓ/ℚ_ℓ): j(s) induces x ↦ x^q on the residue field of ℚ̄_ℓ if and only if s induces x ↦ x^q on that of A.")))))));
}
