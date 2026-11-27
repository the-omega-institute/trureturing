using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme;

internal sealed class TangentCoordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tangent Coords", H("Tangent Coords"),
        Blocks(
            Paragraph(Text("Lie algebra via étale charts and square-zero extensions; action matrices; signature condition.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/TangentCoords.nsmul_injective_and_eq_zero"),
                H("nsmul_injective_and_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A → S be smooth of constant relative dimension, Spec C → S factor through a local ring, y ∈ A(C) vanish modulo a square-zero ideal, m ∈ ℕ. If m is invertible in C, my = 0 forces y = 0; if m = 0 in C, my = 0.")))))));
}
