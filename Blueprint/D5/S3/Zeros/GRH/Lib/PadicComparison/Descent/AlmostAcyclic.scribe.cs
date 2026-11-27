using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Descent;

internal sealed class AlmostAcyclicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Almost Acyclic", H("Almost Acyclic"),
        Blocks(
            Paragraph(Text("Almost acyclicity of the tilted structure sheaf for perfect algebras on p-adic tests.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/AlmostAcyclic.isAcyclicAt_almostCoeff"),
                H("isAcyclicAt_almostCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Almost descent: if π = ξ mod p kills the O^♭-module N and b is a perfect O^♭-algebra, then on p-adic tests S the functor Hom(b, S^♭) with coefficients S^♭ ⊗ N ⊗ 𝔪 has cohomology b ⊗ N ⊗ 𝔪, in degree 0.")))))));
}
