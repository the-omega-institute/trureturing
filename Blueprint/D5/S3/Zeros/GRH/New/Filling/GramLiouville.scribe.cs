using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class GramLiouvilleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram Liouville", H("Gram Liouville"),
        Blocks(
            Paragraph(Text("Discriminant of lattice points in a subspace; Liouville inequality for Gram determinants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/GramLiouville.sublatticeDisc_mul_index_sq_le"),
                H("sublatticeDisc_mul_index_sq_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let n have dim V columns, adelic combinations of vectors of V, with Hn integral, D = [det nᴴn] ≠ 0 and the columns of YHn in K. Let i be the index of K in the Ô-span of the columns of YHm, m = Filling.sublatticeBasis, d = Filling.sublatticeDisc. Then (d·i)² ≤ D, d > 0 and i ≥ 1.")))))));
}
