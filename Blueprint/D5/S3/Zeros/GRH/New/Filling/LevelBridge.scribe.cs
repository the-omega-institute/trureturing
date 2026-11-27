using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class LevelBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level Bridge", H("Level Bridge"),
        Blocks(
            Paragraph(Text("Dictionary between rational, finite adelic and real coordinates of the filling record. Form, level unit, additive character and level group of the record in local terms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/LevelBridge.intGL_map_reduceAboveG"),
                H("intGL_map_reduceAboveG"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For k in K with reduction s at a chosen place w: the entrywise conjugate of k reduces modulo w to J⁻¹s⁻ᵀJ (case b true); for b false both sides are s.")))))));
}
