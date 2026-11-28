using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class MemberOrthogonalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Member Orthogonality", H("Member Orthogonality"),
        Blocks(
            Paragraph(Text("Forms killed by θ, the reflection sums and one Hecke polynomial have zero theta periods; comparison forms are orthogonal to them.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/MemberOrthogonality.stdClassSum_inner_productForm_eq_zero"),
                H("stdClassSum_inner_productForm_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let O satisfy FitsParams, ψ ≠ 1 on Q, 2|r| + 2|N| + 3 < |n|, M² = (ϖ), and Ξ killed by θ, the reflection sums and one Hecke polynomial at AuxPair.testValue. Then the level-ϖ class sum over h of ⟨DividedSplitting.productForm(x, h)(y, conj kernelVector(g, h)), Ξ⟩ vanishes.")))))));
}
