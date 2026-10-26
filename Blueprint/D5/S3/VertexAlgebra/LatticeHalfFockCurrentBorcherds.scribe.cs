using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentBorcherdsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All signed fractional current Borcherds coefficients on the actual tensor module.",
        H("Fractional Current Borcherds Identity"),
        Blocks(
            Paragraph(Text("Let D be arbitrary LatticeData, hu:IsUnit D.G.det, i:Fin D.rank, b:Carrier D, delta,p,q,r integers, and x:ActualTensor(D,hu). The source Carrier D and actual tensor module remain distinct. Write F(u)=correctedField(D,hu,u), A(k)=tensorCurrent(D,ActualGround(D,hu),i,k), S(r,t)=F(neutralMode(D,i,r,b)).coeff(-2*t-delta-3)x, and N=vectorFrequencyBound(D,b)+1. The natural summation indices are cast to integers inside every mode and coefficient exponent.")),
            Paragraph(Text("The three term sequences are L(j)=Ring.choose((p:Complex)+1/2,j) times S(r+j,p+q-j), R1(j)=(-1)^j Ring.choose((r:Complex),j) times A(p+r-j)(F(b).coeff(-2*(q+j)-delta-2)x), and R2(j)=(-1)^j Ring.choose((r:Complex),j) times ((-1:Complex)^r times F(b).coeff(-2*(q+r-j)-delta-2)(A(p+j)x)). The power in (-1)^j is natural, whereas (-1)^r is the signed integer power. The fractional binomial argument p+1/2 is essential.")),
            Paragraph(Text("Let h(i)=neutralMode(D,i,-1,vacuum(D)). The source stateField_current gives mu(D,h(i),n,b)=neutralMode(D,i,n,b). Expanding Corr on the empty word and the zero-charge exponential proves that F(vacuum).coeff(e)x is x at e=0 and zero otherwise. Negative singleton insertion then gives F(h(i)).coeff(-2*k-3)x=A(k)x. These identities are consumed by the source and second ordered support proofs, using the respective native Hahn orders. The source bound N is retained in the finite transforms and the high-order seed.")),
            Paragraph(Text("Prove finite support separately. The left sequence vanishes as soon as r+j>=N by neutralMode truncation on the original source b. The first ordered sequence vanishes when the inner coefficient of F(b)x falls below its Hahn order. The second vanishes when p+j passes the actual current truncation bound of x. Scalar weights preserve these supports. Neither eigenstate support nor cancellation of the complete residue replaces either ordered support.")),
            Paragraph(Text("For p=0, use the complete ordered currentResidue from LatticeHalfFockNegativeCurrentResidue. The negative insertion triangle and positive residue formula combine to give S(r,t)=sum_j Ring.choose(-1/2,j) currentResidue(r+j,t-j) at every finite original-source cutoff. For nonnegative r the same inverse follows from the positive formula. Finite triangular exchange and Ring.add_choose_eq show that convolution by choose(-1/2,j) and choose(1/2,j) are inverse: their convolution is choose(0,j), which selects j=0. Apply this cancellation to obtain currentResidue(r,t)=sum_j Ring.choose(1/2,j) S(r+j,t-j) for every signed r. Every exchanged sum is finite, including the zero-cutoff case.")),
            Paragraph(Text("At r>=N the left sequence is zero. The nonnegative r binomial truncates both ordered sums to range(r+1). Reflect the second ordering by j -> r-j; the identity (-1)^r*(-1)^(r-j)=(-1)^j retains its sign. Ward turns each commutator into a finite sum of source coefficients. Their exponent is -2*(p+q+r-n)-delta-3, independent of the reflection index. The r-th Pascal difference of choose(p+r-j+1/2,n) is zero for n<N<=r. This proves the high-r seed without a target locality or compatibility premise.")),
            Paragraph(Text("Let E(p,q,r)=finsum L-finsum R1+finsum R2. The complex Pascal identity and the signed weighted Pascal identity give E(p+1,q,r)=E(p,q+1,r)+E(p,q,r+1). The three supports justify every split and subtraction of finsums. Induction on nonnegative p uses the p=0 seed. For negative p, induction on the distance below the original cutoff and then on -p uses the same recurrence together with the high-r seed. No restriction on signed p,q,r, delta, the original b, or the actual x is introduced.")),
            Describe.Lean(
                DescribeId.Create("half-fock-current-borcherds"),
                DeclarationHandle.Create(Prefix + "current_borcherds"),
                H("The full all-signed current identity with three independent supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For the entire telescope above, each of L, R1 and R2 has finite support and finsum_j L(j)=finsum_j R1(j)-finsum_j R2(j). This includes current zero modes, arbitrary finite sums in both carriers, and every signed p,q,r. There is no positivity, nonzero-rank, source-sector, target-vacuum, or assumed module-law hypothesis. In canonical sectors gamma=delta=1, the unreduced left shift 2 becomes shift 0 with mode increased by one; this is the odd-odd sector carry, not an integer-binomial replacement."))),
                DescribeRole.Theorem),
            Paragraph(Text("The coefficient proof is a repository-derived application of classical twisted-lattice calculus, with the signed Pascal propagation organized as in LatticeAllStateJacobi. The general same-carrier theorem is not applied to the distinct source and target here. Bakalov and Kac, Twisted Modules over Lattice Vertex Algebras, math/0402315, provide the mathematical setting. This current-generator identity does not establish charged-generator compatibility, arbitrary source-product compatibility, oscillator transport, or completion of the Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme. No physical realization is asserted.")))));
}
