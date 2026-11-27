using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class RegularityFrobeniusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regularity Frobenius", H("Regularity Frobenius"),
        Blocks(
            Paragraph(Text("Admissibility under subobjects, tensors, duals; the linear Weil–Deligne Frobenius and killing polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/RegularityFrobenius.of_pairing"),
                H("of_pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F be coarser than 'near 1', T finite free over R with IsAdmissible for F, and T'' ≅ Hom_R(T, R(c)) equivariantly. Then T'' has IsAdmissible for F, and on inertia what kills (s, 0) on T kills (s⁻¹, 0) on T''.")))))));
}
