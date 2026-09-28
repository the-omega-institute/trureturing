using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Promote the imported finite Weyl trace pairing to actual linear independence, spanning, and an explicit reconstruction formula on the full matrix algebra.",
        H("Exact Finite Weyl Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coefficient-extraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/WeylReconstruction.coefficient_extraction"),
                H("Extract a coefficient with the trace pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formula consumes the repository Weyl displacement trace-orthogonality theorem in the actual cyclic-window matrix representation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("word-linearindependent"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/WeylReconstruction.word_linearIndependent"),
                H("Linear independence of all finite Weyl words"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Taking traces against every Weyl adjoint rules out every nonzero linear relation; the nonzero dimension is used explicitly."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("synthesis-surjective"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/WeylReconstruction.synthesis_surjective"),
                H("Spanning without an assumed basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The synthesis map is an injective endomorphism of the finite-dimensional matrix space, hence surjective. No frame completeness assumption is supplied."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-reconstruction"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/WeylReconstruction.weyl_reconstruction"),
                H("Explicit reconstruction of an arbitrary complex matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient of each word is its adjoint trace pairing divided by the dimension. The statement holds in every positive finite cyclic dimension."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-map-zero-iff-weyl"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/WeylReconstruction.linear_map_zero_iff_weyl"),
                H("Extend a zero leakage test to the full local algebra"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A complex-linear map vanishes on the complete local matrix algebra exactly when it vanishes on every actual Weyl word. This is not an operator-norm estimate and does not cover a smaller commutative observation algebra."))), DescribeRole.Theorem))));
}
