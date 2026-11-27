using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.Dual;

internal sealed class ClassSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Sum", H("Class Sum"),
        Blocks(
            Paragraph(Text("Tensors on complementary blocks lie in the Cartan component; integral, isometric, equivariant product. Linearity, Fubini and integrality of class sums weighted by automorphism groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/Dual/ClassSum.cartanProduct"),
                H("cartanProduct"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The bilinear product of vectors of weights kp, km: tensor their Schur images under the N-columns of g and the m-columns of g⁻ᵀ, then apply an integral left inverse of mixedCartan.")))))));
}
