using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class NonUnitalUnitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Non Unital Units", H("Non Unital Units"),
        Blocks(
            Paragraph(Text("Sums over coset representatives are invariant under left translation. Galois descent: invariants span vectors fixed by a Galois-closed subgroup of finite index (semilinear actions). Spanning set contains a basis of columns; units along non-unital ring maps.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/NonUnitalUnits.exists_GL_col_mem_of_span"),
                H("exists_GL_col_mem_of_span"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a set s spans K^n over a field K, some invertible n×n matrix has all its columns in s.")))))));
}
