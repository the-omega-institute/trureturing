using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedJacobiFiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed all-source two-twisted-input mixed Jacobi law",
        H("The signed all-source two-twisted-input mixed Jacobi law"),
        Blocks(
            Paragraph(Text("MixedJacobiCoefficients owns the actual finite coefficient transports and both ordered source products. MixedJacobiCommonCube combines them on the full target grade. The remaining argument proves finite support in the original restricted dual, evaluates every grade, and extends by the actual finite source and input expansions.")),
            Describe.Lean(DescribeId.Create("actual-full-signed-mixed-jacobi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_jacobi"),
                H("The full identity in the actual fixed restricted dual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every signed m,n,r, every original theta-fixed source a, and both actual negative-parity inputs u,v, the sum choose(m,j) I_(m+n-j)(a_(r+j)u,v) equals the sum (-1)^j choose(r,j) times [a_(m+r-j) I_(n+j)(u,v)-(-1)^r I_(n+r-j)(u,a_(m+j)v)]. Here the output source action is oppositeAction on FixedRestrictedDual, and both input actions are fixedParitySlice. No equality of the source and its dual, symmetry or positivity of actualForm, or dimension of fusion spaces is assumed.")),
                    Paragraph(Text("On homogeneous inputs and source, the target grade is H+K+d-m-n-r-2. The two input branches and the dual-action branch are placed in the same p,q,L cube. Their phases and the all-source iterate identity give the desired equality on every vector of that fixed grade. The normalized homogeneous support and the opposite action's actual grade shift make all other grade evaluations zero, giving equality of the full restricted-dual elements.")),
                    Paragraph(Text("The original source expands through its actual finite energy projections. Each negative-parity twisted input expands through its own finite support in actualAmbientBasis; parity forces those basis vectors to have odd oscillator weight and hence integer energy (oddWeight+3)/2 at rank twenty-four. Linearity extends the proved homogeneous identity to all original fixed sources and actual inputs. Separate truncations of the actual input fields and normalizedCoefficient prove finite support before the finsum operations. The original positive-lattice hypothesis is retained for the opposite action and original negative-grade vanishing. The H=K=2 Leech vacuum coefficient remains I3; three-M crossing is a separate mathematical block."))),
                DescribeRole.Theorem))));
}
