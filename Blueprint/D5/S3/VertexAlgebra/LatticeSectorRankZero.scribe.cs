using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeSectorRankZeroDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank zero sector fields", H("LatticeSectorRankZero"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorrankzero-coordinates"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorRankZero.rankZeroCoordinates"),
                H("rankZeroCoordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("With no oscillator variables the oscillator algebra is canonically the complex scalar algebra. This coordinate map is consumed by the exact rank-zero field calculation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorrankzero-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorRankZero.rankZero_field"),
                H("rankZero_field"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every charge is zero. The actual mixed field in scalar coordinates is scalar multiplication in mode minus one and zero in every other mode. The general classification and category-level universal equivalence retain this rank and give a one-dimensional IO space."))), DescribeRole.Theorem),
            Paragraph(Text("Classical free-boson conventions follow Bakalov-Kac and Matsuo-Nagatomo. This is the scalar boundary of the neutral sector theory, with no full charged lattice module, braiding, associator or CFT assertion.")))));
}
