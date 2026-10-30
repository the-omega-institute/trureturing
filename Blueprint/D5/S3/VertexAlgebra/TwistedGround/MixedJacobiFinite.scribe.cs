using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedJacobiFiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed all-source two-twisted-input mixed Jacobi law",
        H("The signed all-source two-twisted-input mixed Jacobi law"),
        Blocks(
            Paragraph(Text("All calculations retain the original lattice Carrier, actual twisted tensor carrier, actual source L1 and ordered selected actualForm. The twisted inputs are the negative parity space at rank twenty-four. Actual integer conformal weights start at two; this is used also for zero and weight-one transformed outputs.")),
            Paragraph(Text("The first ordered source product has the original b-mode on the right. On the required test grade E=H+K+d-m-n-r-2 its rightmost output weight is K+d-m-1-p-k. The second ordered product has the lowered original a-mode on the right, of output weight H+d-r-1-q-L-k. Thus p+k<=K+d-m-3 and q+L+k<=H+d-r-3 are actual nonzero-support conditions. These conditions precede every finite convolution.")),
            Paragraph(Text("Two applications of the supported signed Vandermonde identity use the finite maps (j,h) to (t=j+h,j), then (ell,t) to (k=ell+t,ell). Their inverse subtractions occur only under the relevant triangle inequalities. They give (-1)^k choose(B-r-L,k), including negative signed r and B. The factorial contraction uses the independent actual original-source nilpotence cutoff.")),
            Paragraph(Text("The source supplier is GroundRightCurrentTransport.FirstSourceClosure.first_eigen_arbitrary_second, applied to the actual lowered theta-fixed first source and arbitrary original second source. Its three finite support clauses and both ordered terms are retained. The calculations are repository derivations using existing actual covariance, lowering, source inversion and all-source compatibility. They do not assert identification of the fixed restricted dual with the original source, a positive or symmetric selected form, three-twisted crossing, or a complete VOA construction.")),
            Paragraph(Text("The complete second-input outer branch first bounds z by actual original-source nilpotence, gathers ell,z at L and reorders the resulting finite sums. Its external (-1)^r makes its phase C=(-1)^(n+1-p-H+q+d)/(p!q!L!). The first-input phase is -C(-1)^R, where R=2d-L-m-r-2. Input lowering bounds p<K-1 and q<H-1, original source nilpotence, and the two actual ordered-product weight bounds permit padding to one common finite cube before the contractions are combined.")),
            Describe.Lean(DescribeId.Create("actual-first-input-finite-reindexing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_first_input_reindexed_pairing"),
                H("First-input triangle on the actual signed support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed output-energy alternative is consumed before padding. The map q_target=i+L+h has the inverse h=q_target-i-L on its finite triangle. The rightmost actual source mode has weight H+d-r-1-i-L-j-h, so integer weights below two make every padding term zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-all-source-finite-cancellation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_source_finite_cancellation"),
                H("Both ordered actual source products after signed contraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The public first_eigen_arbitrary_second supplier is applied with the lowered fixed source, gamma=delta=0 and P=r, Q=2H-n-r-2+p-q, R=2d-L-m-r-2. The two finite signed convolutions retain both ordered products. This conclusion uses the actual three-supported source law, without a mixed-law premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-first-input-entire-branch"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_first_input_branch_reindexed"),
                H("Entire first-input branch at k_source=j+h"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual low-energy vanishing bounds the outer signed input action before the triangle is reindexed and the finite Vandermonde identity is applied. The second ordered source product retains the literal phase (-1)^(m+n+r+2-p-H-d+i+L)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-second-input-finite-reindexing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_second_input_reindexed_pairing"),
                H("Second-input triangle with total lowering L=ell+z"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map p_target=i+ell+h is evaluated after the signed-output split. Transposition retains both original actualForm slots and the original finite source sum. The target first ordered source product has L=ell+z, k_source=j+ell+h and rightmost output weight K+d-m-1-i-k_source."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-second-source-factorials"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_second_source_factorial_contraction"),
                H("Actual total-source factorial contraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original source nilpotence bounds both lowering indices before reindexing ell,z by L=ell+z. The literal factor 1/(ell! z!) becomes choose(L,ell)/L! on the actual first ordered source product. Binomial parameters may be signed; they supply no support premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-full-signed-mixed-jacobi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite.mixed_jacobi"),
                H("The full identity in the actual fixed restricted dual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every signed m,n,r, every original theta-fixed source a, and both actual negative-parity inputs u,v, the sum choose(m,j) I_(m+n-j)(a_(r+j)u,v) equals the sum (-1)^j choose(r,j) times [a_(m+r-j) I_(n+j)(u,v)-(-1)^r I_(n+r-j)(u,a_(m+j)v)]. Here the output source action is oppositeAction on FixedRestrictedDual, and both input actions are fixedParitySlice. No equality of the source and its dual, symmetry or positivity of actualForm, or dimension of fusion spaces is assumed.")),
                    Paragraph(Text("On homogeneous inputs and source, the target grade is H+K+d-m-n-r-2. The two input branches and the dual-action branch are placed in the same p,q,L cube. Their phases and the all-source iterate identity give the desired equality on every vector of that fixed grade. The normalized homogeneous support and the opposite action's actual grade shift make all other grade evaluations zero, giving equality of the full restricted-dual elements.")),
                    Paragraph(Text("The original source expands through its actual finite energy projections. Each negative-parity twisted input expands through its own finite support in actualAmbientBasis; parity forces those basis vectors to have odd oscillator weight and hence integer energy (oddWeight+3)/2 at rank twenty-four. Linearity extends the proved homogeneous identity to all original fixed sources and actual inputs. Separate truncations of the actual input fields and normalizedCoefficient prove finite support before the finsum operations. The original positive-lattice hypothesis is retained for the opposite action and original negative-grade vanishing. The H=K=2 Leech vacuum coefficient remains I3; three-M crossing is a separate mathematical block."))),
                DescribeRole.Theorem))));
}
