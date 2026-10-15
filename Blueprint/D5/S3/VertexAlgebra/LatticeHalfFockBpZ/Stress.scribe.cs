using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class StressDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual native half-Fock Virasoro modes have reflected bilinear adjoints.",
        H("Native Stress Reflection and Grade Orthogonality"),
        Blocks(Describe.Lean(
            DescribeId.Create("tensorstressadjoint"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Stress.tensor_stress_adjoint"),
            H("The Adjoint of L(m) is L(-m)"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Transposing an original normally ordered current pair introduces two minus signs and reverses the order. Reflection of each half-index selects precisely the reflected original normal ordering. The original statewise finite normal sum permits applying each pairing functional before reindexing the integer sum by j -> -j-1.")),
                Paragraph(Text("The same inverse-Gram coefficient matrix appears in both arguments without conjugation. The original rank/16 scalar correction remains at mode zero. Tensoring the oscillator identity yields the native Virasoro adjoint. Self-adjointness of nativeL0 forces distinct complex eigenvalues to be bilinearly orthogonal. This is a mode identity on the original tensor, not an assertion of full all-state vertex-algebra invariance."))),
            DescribeRole.Theorem))));
}
