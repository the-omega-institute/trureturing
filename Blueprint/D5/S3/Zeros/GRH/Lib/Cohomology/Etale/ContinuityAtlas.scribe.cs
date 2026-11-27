using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class ContinuityAtlasDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity Atlas", H("Continuity Atlas"),
        Blocks(
            Paragraph(Text("Cohomology turns filtered limits of relatively affine functors into colimits; base change functors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/ContinuityAtlas.of_atlas"),
                H("of_atlas"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If q: h_T → Y is relatively representable (affine) with dense image on test rings for locally constant Λ-valued functions, then Λ-cohomology turns small filtered limits of functors affine over Y into colimits (IsCohomContinuous).")))))));
}
