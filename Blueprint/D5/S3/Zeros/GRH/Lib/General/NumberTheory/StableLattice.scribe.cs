using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class StableLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable Lattice", H("Stable Lattice"),
        Blocks(
            Paragraph(Text("Integer rings of finite Galois extensions of Q_ℓ: DVR, compact, directed; length versus cardinality. Compact groups in GL_n of l-adic closure stabilise a lattice; integral characteristic polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/StableLattice.eventually_exists_isLatticeIn"),
                H("eventually_exists_isLatticeIn"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A continuous representation of a compact group G on ℚ̄_ℓ^n is conjugate to one with entries in O, for every large enough ring of integers O of a finite extension of ℚ_ℓ.")))))));
}
