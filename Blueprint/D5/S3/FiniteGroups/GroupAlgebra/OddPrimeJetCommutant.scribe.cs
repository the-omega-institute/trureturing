using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetCommutantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full prime-field-linear commutant of the original odd-prime jet action",
        H("Actual actions and unrestricted top endomorphisms"),
        Blocks(
            Paragraph(Text("Let p be any odd prime, including three, F=ZMod p, and K any field with an F-algebra structure. The universe of K is independent. No finiteness, finite-dimensionality, perfection or nonzero-q assumption is imposed. The carrier remains V=Polynomial.degreeLT K p and the action remains the originalRepresentation q supplied by OddPrimeJetDeformation, with normalized arbitrary F-linear q satisfying q(1)=0. Every candidate X is only F-linear.")),
            Describe.Lean(
                DescribeId.Create("odd-prime-jet-actual-unique-commutant"),
                DeclarationHandle.Create(Prefix + "actual_commutant_iff_unique_toeplitz"),
                H("The unique actual-action normal form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write N=d/dt and m(a) for coefficientwise scalar multiplication. X commutes with every original action operator if and only if it has one unique expression X=sum_(0<=r<p-1) m(a_r) N^r + T N^(p-1), with a_r in K and an arbitrary T in End_F(K). Here the last term means: apply N^(p-1), read its constant coefficient, apply T, then embed as a constant polynomial. T need not be scalar multiplication, injective, surjective or K-linear.")),
                    Paragraph(Text("OddPrimeJetCommutantCore proves the original-action generated bridge, the degree normal form, its injectivity, the explicit coordinatesEquiv and the actual-operator unit criterion. This entry module proves toeplitz_as_degree and the bijection between c with c(0)=0 and ordinary shift coordinates a_r=c_(p-1-r); it applies core existence and injectivity to obtain the unique displayed pair.")),
                    Paragraph(Text("The characterization has no q on its coordinate side. Consequently the commutants of all normalized q are equal, including zero and singular q. This consequence concerns the commutant; the original labeled actions and their intertwining conditions are not identified.")),
                    Paragraph(Text("For a fixed parameter automorphism and two existing intertwiners P,Q, their ratio Q P^(-1) is an invertible element of the source or target commutant according to composition order. Extra nonscalar F-linear top maps therefore enlarge the possible lifts of an already admissible parameter change. They do not create new admissible parameter changes: that existence criterion is the separate original-pair classification supplier. Finite-field coefficient orbit classes and the full intertwiner-group splitting require their own results and do not follow from the commutant theorem alone."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-prime-jet-commutant-product"),
                DeclarationHandle.Create(Prefix + "toeplitzDegree_mul"),
                H("Composition and the noncentral top maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For X=(a,T) and Y=(b,U), multiplication is operator composition XY(v)=X(Y(v)). The lower coefficient of N^k is sum_(i+j=k) a_i*b_j. The top map is m(a_0) composed with U + T composed with m(b_0) + m(sum_(1<=i<=p-2) a_i*b_(p-1-i)). The two compositions retain their order. In particular the top maps form a square-zero ideal whose left and right K-actions may differ; the resulting extension need not be commutative in general, while the prime-field case K=F is commutative.")),
                    Paragraph(Text("The kernel proof uses productFamily and topConvolution in the verified degree indexing: the output-degree-j scalar is sum_(i+k=p-1+j) c_i*d_k for j>0, and the additional scalar in the top map is sum_(i+k=p-1) c_i*d_k. With c_0=d_0=0 and a_r=c_(p-1-r), b_r=d_(p-1-r), these are exactly the preceding shift convolutions. Positive derivative powers annihilate every top output, and a top map annihilates every positive-shift input. These identities verify the orientation on actual operators."))),
                DescribeRole.Theorem))));
}
