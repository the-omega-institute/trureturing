using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetReconstruction", H("Finite transport through native normal products"), Blocks(
            Paragraph(Text("For native truncated fields, suppose each coefficient on an injected old target is the finite convolution of a longitudinal field with a family of linear creation maps. Suppose negative current modes commute through every creation map and nonnegative current modes transport the target injection. Then the same finite convolution holds after native normalMinusOne. For a fixed target, negative terms have indices i,j with i+j below the native field cutoff, hence finite support on pairs. Positive terms have finitely many current indices i, and each resulting target has its own field cutoff in j. These two finite supports justify the exchanges of coefficient sums. The private native_normal_separation lemma is consumed by the all-source inner_creation_expansion; it introduces no new vertex algebra or assumed contraction law. Native normal products follow Bakalov-Kac, math/0402315v1, section 4.1.")))));
}
