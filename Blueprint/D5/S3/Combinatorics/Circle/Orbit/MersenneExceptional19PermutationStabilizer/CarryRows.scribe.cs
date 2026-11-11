using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer;

internal sealed class CarryRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral physical exceptional19 CarryRows.", H("Integral physical CarryRows"),
        Blocks(
            Describe.Lean(DescribeId.Create("carry-step"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows.carry_step"),
                H("carry step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both physical endpoints lie in the proved affine ranges. Subtracting their zero readings and applying the signed binary-carry identity gives the actual G, F and H equations. The group proof uses integer linear combinations and retains arbitrary torsion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-annihilates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows.affine_annihilates"),
                H("affine annihilates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both physical endpoints lie in the proved affine ranges. Subtracting their zero readings and applying the signed binary-carry identity gives the actual G, F and H equations. The group proof uses integer linear combinations and retains arbitrary torsion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("g-equation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows.g_equation"),
                H("g equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both physical endpoints lie in the proved affine ranges. Subtracting their zero readings and applying the signed binary-carry identity gives the actual G, F and H equations. The group proof uses integer linear combinations and retains arbitrary torsion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("f-equation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows.f_equation"),
                H("f equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both physical endpoints lie in the proved affine ranges. Subtracting their zero readings and applying the signed binary-carry identity gives the actual G, F and H equations. The group proof uses integer linear combinations and retains arbitrary torsion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("h-equation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows.h_equation"),
                H("h equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both physical endpoints lie in the proved affine ranges. Subtracting their zero readings and applying the signed binary-carry identity gives the actual G, F and H equations. The group proof uses integer linear combinations and retains arbitrary torsion."))), DescribeRole.Theorem),
Paragraph(Text("This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers."))), []));
}
