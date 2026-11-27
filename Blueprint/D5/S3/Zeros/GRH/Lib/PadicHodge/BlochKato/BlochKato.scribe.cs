using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.BlochKato;

internal sealed class BlochKatoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bloch Kato", H("Bloch Kato"),
        Blocks(
            Paragraph(Text("Bloch–Kato rank formula for crystalline cocycles; positive weights and cyclotomic twists as consequences.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/BlochKato.apply_eq_zero_of_cyclotomicGp"),
                H("apply_eq_zero_of_cyclotomicGp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Γ act on T, finite free over Z_p, through χ^(−a) with a ≥ 0. A crystalline cocycle c vanishes at every s with ρ(s) = 1, provided j(s) lies in inertia when a = 0.")))))));
}
