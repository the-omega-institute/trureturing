using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProjectiveLine;

internal sealed class PerfectLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfect Line", H("Perfect Line"),
        Blocks(
            Paragraph(Text("Perfected projective line from two perfect discs: tilted cohomology relative to infinity vanishes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/PerfectLine.subsingleton_coker_gluing"),
                H("subsingleton_coker_gluing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If ℤ[h_c]⊗i induces bijections on all Ext^n(−, F) for every p-adic test c (i = gluing), then Ext^n(S⊗coker i, F) = 0 for every flat S and every n.")))))));
}
