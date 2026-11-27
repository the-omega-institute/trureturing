using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma;

internal sealed class GaloisOnFramesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois On Frames", H("Galois On Frames"),
        Blocks(
            Paragraph(Text("Galois stability of the Kisin lattice; congruence step towards triviality modulo the variable.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/GaloisOnFrames.smul_mem_kisinAinf"),
                H("smul_mem_kisinAinf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If g in Γ satisfies gΓ'g⁻¹ ⊂ Γ', then g maps the module Lift.KummerChart.JumpLattice.kisinAinf of L into itself.")))))));
}
