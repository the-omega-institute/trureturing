using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class DepthVanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Depth Vanishing", H("Depth Vanishing"),
        Blocks(
            Paragraph(Text("Local cohomology vanishes below the depth; Zariski descent for Hodge tests.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/DepthVanishing.hasZariskiDescent_hodgeCoeff"),
                H("hasZariskiDescent_hodgeCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Open covers are dense for Hodge cohomology: the coefficients (A,M) ↦ ⋀_A M satisfy Zariski descent HasZariskiDescent for the rings A ⊕ M.")))))));
}
