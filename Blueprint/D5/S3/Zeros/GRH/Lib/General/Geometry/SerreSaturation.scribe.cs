using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class SerreSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Serre Saturation", H("Serre Saturation"),
        Blocks(
            Paragraph(Text("Serre: sections of high powers of a very ample bundle are forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/SerreSaturation.eventually_span_coordSection"),
                H("eventually_span_coordSection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Serre's theorem: let N be a projective embedding of an integral scheme A over a field, p : A' → A a base change to a noetherian ring k. For large m, the degree m monomials in the coordinates span H⁰((p^*N)^m) over k.")))))));
}
