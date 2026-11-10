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
                    Paragraph(Text("The supplier polynomial_log_action recovers L_q(a)=aN+q(a)N^(p-1) from the original action using coefficients in F. Conversely commuting with all L_q(a) gives commuting with their finite exponentials. Since L_q(1)=N, commutation gives commutation with N. Composing L_q(a) with N^(p-2) kills the deformation term, because 2p-3>=p, and yields m(a)N^(p-1). Subtracting this highest term from L_q(a) then recovers every m(a)N. All inequalities retain p=3. The original labeled representation is preserved; only its commutant is described by these generated operators.")),
                    Paragraph(Text("For e_j(z)=z*t^j/j!, e_j(z)=N^(p-1-j)e_(p-1)(z). Thus a commuting X is determined by X(e_(p-1)(z)). Reconstruction in divided monomials and commutation with m(a)N show that all its positive-degree coefficient maps are K-linear: A_j(a*z)=a*A_j(z) for j>0, hence A_j(z)=A_j(1)*z. The degree-zero coefficient map remains arbitrary F-linear. Evaluation on top vectors proves uniqueness and the converse uses the vanishing products of the top term with m(a)N.")),
                    Paragraph(Text("The definition coordinatesEquiv is an explicit two-sided equivalence from the actual commutant subtype to the scalar coordinates and End_F(K), with inverse the displayed actual polynomial operator. Internally the scalar family is indexed by output degree j: c_0=0 and a_r=c_(p-1-r). This convention makes the top coefficient map visible without duplicating it as a scalar coordinate. toeplitz_as_degree verifies the change to the ordinary shift indexing.")),
                    Paragraph(Text("The characterization has no q on its coordinate side. Consequently the commutants of all normalized q are equal, including zero and singular q. This consequence concerns the commutant; the original labeled actions and their intertwining conditions are not identified."))),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-prime-jet-commutant-unit"),
                DeclarationHandle.Create(Prefix + "toeplitzDegree_isUnit_iff"),
                H("Units over arbitrary K"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The actual F-linear operator is a unit if and only if a_0 is nonzero, equivalently c_(p-1) is nonzero. Any operator commuting with N and killing constants has p-th power zero: induct on the derivative-kernel filtration and use N^p=0. A zero leading scalar therefore makes X nilpotent. When a_0 is nonzero, Z=m(a_0^(-1))X-I commutes with N and kills constants, so Z^p=0. The finite nilpotent geometric inverse makes I+Z a unit, and X=m(a_0)(I+Z). The proof uses actual endomorphisms and requires no finite dimension over F.")),
                    Paragraph(Text("For a fixed parameter automorphism and two existing intertwiners P,Q, their ratio Q P^(-1) is an invertible element of the source or target commutant according to composition order. Extra nonscalar F-linear top maps therefore enlarge the possible lifts of an already admissible parameter change. They do not create new admissible parameter changes: that existence criterion is the separate original-pair classification supplier. Finite-field coefficient orbit classes and the full intertwiner-group splitting require their own results and do not follow from the commutant theorem alone.")),
                    Paragraph(Text("The polynomial action, finite exponential/logarithm, divided monomials and derivative-kernel suppliers retain their attribution in OddPrimeJetDeformation and the original-pair sources. The block-Toeplitz centralizer argument is classical; a broader reference is Drensky, Szigeti and van Wyk, Centralizers in endomorphism rings, arXiv:0910.2357. Nilpotent-unit calculus is reused from pinned Mathlib.RingTheory.Nilpotent.Basic. This development makes no literature-priority claim."))),
                DescribeRole.Theorem))));
}
