using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Kunneth;

internal sealed class LerayHirschBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Leray Hirsch Basis", H("Leray Hirsch Basis"),
        Blocks(
            Paragraph(Text("Künneth in Leray–Hirsch form over the special fibre, passed from geometric points to tests.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Kunneth/LerayHirschBasis.exists_lerayHirsch_basis"),
                H("exists_lerayHirsch_basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let M satisfy IsDetectedAtPoints, with the locus 𝔪_A = 0 dense. Some set b of homogeneous classes in Ext(L∘g, M), L the locally constant ℤ/ℓ-valued functions, has bijective Leray–Hirsch map at ℤ[h_c] for every test c killing 𝔪_A, and contains j if j(1) ≠ 0.")))))));
}
