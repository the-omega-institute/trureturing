using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class GaloisRepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois Rep", H("Galois Rep"),
        Blocks(
            Paragraph(Text("Hodge–Tate images of distinct point classes on a projective variety are linearly independent. Half of holomorphic Lefschetz formula: killed Hodge–Tate classes force vanishing local term sums. Galois representation from cohomology: good reduction, Eichler–Shimura relation, Hodge–Tate weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/GaloisRep.exists_galois_rep"),
                H("exists_galois_rep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a model of neat level over a localisation of O_E where safe primes survive, σ : ℂ ≅ ℚ̄_ℓ, and J supported at σ|E, in weights where θ occurs, some continuous ρ : Gal(Ω/E) → GL_N(ℚ̄_ℓ) satisfies SphericalClause at each safe w, with jumps including J and the Hecke polynomial of σθ_w.")))))));
}
