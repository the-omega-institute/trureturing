using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedJacobiFiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported finite reindexing for the actual mixed coefficient law",
        H("Supported finite reindexing for the actual mixed coefficient law"),
        Blocks(
            Paragraph(Text("All calculations retain the original lattice Carrier, actual twisted tensor carrier, actual source L1 and ordered selected actualForm. The twisted inputs are the negative parity space at rank twenty-four. Actual integer conformal weights start at two; this is used also for zero and weight-one transformed outputs.")),
            Paragraph(Text("The first ordered source product has the original b-mode on the right. On the required test grade E=H+K+d-m-n-r-2 its rightmost output weight is K+d-m-1-p-k. The second ordered product has the lowered original a-mode on the right, of output weight H+d-r-1-q-L-k. Thus p+k<=K+d-m-3 and q+L+k<=H+d-r-3 are actual nonzero-support conditions. These conditions precede every finite convolution.")),
            Paragraph(Text("Two applications of the supported signed Vandermonde identity use the finite maps (j,h) to (t=j+h,j), then (ell,t) to (k=ell+t,ell). Their inverse subtractions occur only under the relevant triangle inequalities. They give (-1)^k choose(B-r-L,k), including negative signed r and B. The factorial contraction uses the independent actual original-source nilpotence cutoff.")),
            Paragraph(Text("The source supplier is GroundRightCurrentTransport.FirstSourceClosure.first_eigen_arbitrary_second, applied to the actual lowered theta-fixed first source and arbitrary original second source. Its three finite support clauses and both ordered terms are retained. The calculations are repository derivations using existing actual covariance, lowering, source inversion and all-source compatibility. They do not assert identification of the fixed restricted dual with the original source, a positive or symmetric selected form, three-twisted crossing, or a complete VOA construction.")),
            Paragraph(Text("The full signed mixed restricted-dual law additionally requires assembling the entire second-input branch, the common outer finite lowering sums and phases, and the actual fixed-grade, off-grade and finite homogeneous extensions. No such full law is asserted by the finite coefficient endpoints here.")),
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
                Blocks(Paragraph(Text("Original source nilpotence bounds both lowering indices before reindexing ell,z by L=ell+z. The literal factor 1/(ell! z!) becomes choose(L,ell)/L! on the actual first ordered source product. Binomial parameters may be signed; they supply no support premise."))), DescribeRole.Theorem))));
}
