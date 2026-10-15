using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class SectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original theta-odd W submodule inherits a symmetric nondegenerate complex-bilinear form.",
        H("Restriction to the Original Theta-Odd Sector"),
        Blocks(Describe.Lean(
            DescribeId.Create("wpairingnondegenerate"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Sector.w_pairing_nondegenerate"),
            H("Nondegeneracy on W"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The original sigmaTensor negates the oscillator variables and fixes the chosen ground. Polynomial induction, the native creation adjoint, and the original derivative-negation identity prove invariance of tensorPairing. Thus sigmaTensor is self-adjoint, and its opposite eigenspaces are orthogonal.")),
                Paragraph(Text("NativeW is exactly oddTarget, the kernel of sigmaTensor plus the identity. The actual projection is (v-sigmaTensor(v))/2. Pairing an odd state against this projection agrees with pairing against the original vector. A vector in either restricted radical would therefore lie in the corresponding full tensor radical. wPairing is obtained through the two original subtype maps, with no replacement sector or assumed isometry."))),
            DescribeRole.Theorem))));
}
