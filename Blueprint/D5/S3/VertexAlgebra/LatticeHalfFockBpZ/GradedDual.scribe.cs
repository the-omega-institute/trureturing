using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class GradedDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Leech theta-odd W is isomorphic through its actual BPZ form to its restricted integral graded dual.",
        H("Actual W Graded Self-Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("gradedwselfdualityevaluation"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/GradedDual.graded_w_self_duality_evaluation"),
            H("Restricted Dual Evaluation is the Original Pairing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The existing rank-24 integer direct-sum decomposition and exact integralSector/eigenspace equality assemble the original W carrier from its actual integral grades. Each grade is identified with its algebraic dual by the nondegenerate restricted tensor pairing, using proved finite native grades. Applying these equivalences componentwise gives gradedWSelfDuality from NativeW to the direct sum, not the unrestricted product, of those duals.")),
                Paragraph(Text("Direct-sum induction and native grade orthogonality show that evaluation on a homogeneous test vector equals tensorPairing of the original state and test vector. This establishes genuine complex-bilinear graded self-duality on the literal chosen-ground Leech tensor. It does not supply the charged-field coefficient adjoint, full twisted Jacobi, all-j identities, WW gluing, a full orbifold, a string theory or an AdS/CFT correspondence."))),
            DescribeRole.Theorem))));
}
