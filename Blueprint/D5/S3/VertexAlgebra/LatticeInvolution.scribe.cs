using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeInvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeInvolution.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection on the actual ordinary-lattice fields gives a fixed vertex algebra and all-mode sign selection.",
        H("Actual Lattice Reflection and Its Fixed Vertex Algebra"),
        Blocks(
            Paragraph(Text("Let D have finite rank r, including r=0, an integral "
                + "symmetric Gram matrix G, and even diagonal. Charges are "
                + "L=(Fin(r) to Z), and B(a,b)=sum_i,j a_i G_ij b_j. The actual "
                + "carrier is the finite charge sum of complex multivariate "
                + "polynomials in oscillator variables X_(i,k), with i in Fin(r) "
                + "and k in N. Its already constructed Y, vacuum and translation "
                + "T are used throughout. Neither positivity nor nondegeneracy "
                + "nor finite grading is required; degenerate and indefinite "
                + "forms are included. No automorphism, cochain or desired "
                + "field-compatibility law is a premise.")),
            Describe.Lean(
                DescribeId.Create("actual-reflection-square"),
                DeclarationHandle.Create(Prefix + "theta_involutive"),
                H("Charge reflection negates every oscillator and squares to identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Define sigma by polynomial evaluation "
                        + "X_(i,k) to -X_(i,k), fixing each complex constant. "
                        + "Define the complex-linear theta by "
                        + "theta(single(a,p))=single(-a,sigma(p)). This acts on "
                        + "every oscillator index, rather than just on charge. "
                        + "Polynomial induction proves sigma squared is identity; "
                        + "finite-charge linear extension proves theta squared "
                        + "is identity and gives an actual linear equivalence."))),
                DescribeRole.Theorem),
            Paragraph(Text("Positive-rank application of existing results. "
                + "For every lattice datum D as above with 0 < D.rank, "
                + "theta D is not LinearEquiv.refl over the complex numbers on "
                + "Carrier D, and orderOf(theta D)=2 in the group of complex-linear "
                + "self-equivalences. These are consequences of the reflection "
                + "formulas and the prime-order criterion, with the following "
                + "explicit parameter correspondence.")),
            Paragraph(Text("Set i to the element of Fin(D.rank) with value 0, "
                + "using the positive-rank hypothesis for its bound. Take charge "
                + "a=0 and oscillator index x=(i,0), and put "
                + "v=Finsupp.single(0,MvPolynomial.X(x)) in Carrier D. "
                + "The pinned MvPolynomial.X_ne_zero and Finsupp.single_eq_zero "
                + "give v nonzero. Apply LatticeInvolution.theta_single at "
                + "(D,a,p)=(D,0,X(x)) and LatticeInvolution.sigma_X at (D,x). "
                + "Since -0=0 and single preserves negation, theta D v=-v. "
                + "This is an actual state of the same carrier and reflection, "
                + "rather than an independently supplied action or witness.")),
            Paragraph(Text("If theta D were the identity equivalence, evaluating "
                + "that equality at v would also give theta D v=v. Thus -v=v, "
                + "so (2 : C) smul v=v+v=0. Since 2 is nonzero in C, "
                + "smul_eq_zero forces v=0, contradicting the witness. "
                + "Hence theta D is nonidentity. For the exact-order conclusion, "
                + "use the group element g=theta D and the prime p=2 in "
                + "mathlib's orderOf_eq_prime. Extensionality and "
                + "LatticeInvolution.theta_involutive give g^2=1; "
                + "the same oscillator argument gives g!=1. "
                + "The criterion therefore yields orderOf(g)=2.")),
            Paragraph(Text("The sole extra hypothesis in these two conclusions "
                + "is positive rank. The symmetric integral Gram matrix with "
                + "even diagonal remains arbitrary, including degenerate and "
                + "indefinite forms. The square identity still includes rank zero; "
                + "neither nonidentity nor exact order two is asserted there. "
                + "This application of existing results concerns the actual "
                + "complex-linear reflection and makes no additional physical "
                + "realization, resource or literature-novelty claim.")),
            Describe.Lean(
                DescribeId.Create("actual-reflection-vacuum"),
                DeclarationHandle.Create(Prefix + "theta_vacuum"),
                H("The actual vacuum is fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The vacuum is single(0,1). Charge "
                    + "negation fixes zero and sigma fixes the constant one."))),
                DescribeRole.Theorem),
            Paragraph(Text("The realized lower-triangular section obeys c(a,a)=B(a,a)/2 and "
                + "epsilon(a,-a)=(-1)^(B(a,a)/2). The ground formula is "
                + "theta(single(a,1))=(-1)^(B(a,a)/2) smul (epsilon(a,-a) smul single(-a,1))=single(-a,1). "
                + "The section-square equation is the released integral_cocycle_square result. "
                + "Dong-Nagatomo, math/9808088v1, pp. 4-5 and 9, write theta(a)=a inverse times (-1)^q, "
                + "q=B(a,a)/2. Bakalov-Kac, math/0402315v1, section 4.1, equations (4.18)-(4.20), "
                + "Proposition 4.1 and Remark 4.1 give the lift and field context. Their "
                + "positive-definite classification conclusions are outside the present hypotheses.")),
            Describe.Lean(
                DescribeId.Create("actual-all-state-mode-covariance"),
                DeclarationHandle.Create(Prefix + "stateField_theta"),
                H("Every actual integer mode commutes with reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("For arbitrary nonhomogeneous, multi-charge "
                        + "states a,b and every n in Z, "
                        + "theta((Y(a))_n b)=(Y(theta(a)))_n theta(b). "
                        + "The integer n is the same on both sides.")),
                    Paragraph(Text("The charged proof transports the actual "
                        + "creation series, exponential coefficients, translated "
                        + "polynomial coefficients and their exact support, "
                        + "then the finite raw charged convolution. The neutral "
                        + "proof treats the creation, zero and annihilation "
                        + "branches separately; polynomial differentiation "
                        + "anticommutes with sigma. Every divided derivative "
                        + "has sign minus, regardless of its derivative order.")),
                    Paragraph(Text("The two contextual sums in a normal-product "
                        + "coefficient have finite support at the indicated "
                        + "actual vector. Theta transports both sums and retains "
                        + "the order of each composition. Induction on ordered "
                        + "oscillator words gives the sign (-1)^word_length. "
                        + "The monomial basis and finite-charge linear extension "
                        + "then give the displayed all-state law. Internal "
                        + "product compatibility is proved from these concrete "
                        + "generators, without assuming the desired result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-vertex-algebra"),
                DeclarationHandle.Create(Prefix + "fixed_actualVertexAlgebra"),
                H("The actual fixed subtype is a full ungraded vertex algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("The fixed submodule is ker(thetaLinear-id). "
                        + "The actual vacuum belongs to it, and the all-state "
                        + "law closes every integer mode on fixed states. "
                        + "The identity T(a)=a_(-2) vacuum gives translation "
                        + "closure. Restrict these actual modes to the subtype; "
                        + "statewise lower truncation follows from the ambient "
                        + "field's actual Hahn order. Their linear field map "
                        + "is fixedY, not an independently postulated field.")),
                    Paragraph(Text("The constructor contains the actual vacuum "
                        + "field, creation at mode -1, creativity at every "
                        + "n>=0, T(vacuum)=0, [T,a_n]=-n a_(n-1), pairwise "
                        + "locality with an order independent of the test "
                        + "vector, and full integer Borcherds. Inclusion "
                        + "identifies each actual mode. Iterated commutator "
                        + "differences transport locality from the already "
                        + "proved ambient actual vertex algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-full-borcherds"),
                DeclarationHandle.Create(Prefix + "fixed_borcherds"),
                H("Full integer Borcherds and all three finite supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("For fixed a,b,c and arbitrary p,q,r in Z, "
                        + "put mu(a,n,b)=(fixedY(a))_n b and C(k,i)=binom(k,i) "
                        + "for the integer binomial coefficient. For i in N, "
                        + "let L_i=C(p,i) mu(mu(a,r+i,b),p+q-i,c), "
                        + "F_i=(-1)^i C(r,i) mu(a,p+r-i,mu(b,q+i,c)), and "
                        + "S_i=(-1)^i C(r,i) (-1)^r "
                        + "mu(b,q+r-i,mu(a,p+i,c)). All three families "
                        + "L,F,S have finite support, and "
                        + "finsum_i L_i=finsum_i (F_i-S_i). Negative p,q,r "
                        + "are included. The residue sign (-1)^r is separate "
                        + "from epsilon_charge(D,a,b).")),
                    Paragraph(Text("Subtype inclusion preserves each nested "
                        + "summand, reflects zero exactly, and hence identifies "
                        + "the genuine supports. It transports each of the "
                        + "three ambient finite-support proofs and preserves "
                        + "finsums by injectivity. Thus the full equality "
                        + "is inherited without a fixed-algebra compatibility "
                        + "premise or an assumption that divergent sums vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-mode-eigenvalue-selection"),
                DeclarationHandle.Create(Prefix + "mode_eigenvalue_selection"),
                H("Actual mode eigenvalues multiply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For arbitrary complex s,t, the explicit "
                    + "actual equations theta(a)=s a and theta(b)=t b imply "
                    + "theta(a_n b)=(st)(a_n b) for every integer n. "
                    + "In particular (++),(+-),(-+),(--) give signs "
                    + "+,-,-,+. These are state-mode selection laws; no "
                    + "tensor-category fusion or anomaly classification is claimed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The inherited finite residue kernels and divided "
                + "derivatives retain Scott Carnahan/vertexAlg, revision "
                + "4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0 "
                + "source-header attribution. Local normal-product closure and "
                + "reconstruction use Matsuo-Nagatomo, hep-th/9706118v1, "
                + "Proposition 1.5.5 p. 11 and Theorem 5.4.1 p. 35, and the "
                + "pinned mathlib db584cd6d46c92f209a44c0f1c829460d327499d "
                + "vertex-operator infrastructure with its attribution. "
                + "The concrete coefficient, word and subtype arguments here "
                + "are adaptations on this actual carrier.")),
            Paragraph(Text("This result constructs an ungraded fixed vertex "
                + "algebra. Conformal grading, PCT, positivity, Leech "
                + "identification, twisted state-fields, intertwiners, holomorphic "
                + "extension, categorical fusion, Monster identification, string "
                + "theory and AdS/CFT completion remain outside this theorem. "
                + "They are not prerequisites for delivery of this closed unit.")))));
}
