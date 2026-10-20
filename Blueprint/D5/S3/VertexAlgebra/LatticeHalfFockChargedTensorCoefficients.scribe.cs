using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedTensorCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula LatticeParameter => Seq(F.Id("D"), Colon, F.Id("LatticeData"));
    private static Formula GroundParameters => Seq(LatticeParameter, Comma, Sp,
        F.Id("hu"), Colon, Call("IsUnit", Call("det", Call("G", F.Id("D")))));
    private static Formula ChargeParameter => Seq(F.Id("a"), Colon, Call("Charge", F.Id("D")));
    private static Formula PolynomialParameter => Seq(F.Id("p"), Colon, Call("Oscillator", F.Id("D")));
    private static Formula VectorParameter => Seq(F.Id("v"), Colon,
        Call("ActualGround", F.Id("D"), F.Id("hu")));
    private static Formula IntegerParameter(string name) => Seq(F.Id(name), Colon, Mathbb, Grp(F.Id("Z")));
    private static Formula Tensor(Formula polynomial, Formula vector) => Seq(polynomial, F.Id("tensor"), vector);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native charged coefficients on the actual twisted ground module",
        H("Actual Charged Tensor Laurent Coefficients"),
        Blocks(
            Paragraph(Text("Let D be an integral symmetric even-diagonal lattice datum of arbitrary finite rank. "
                + "Assume IsUnit D.G.det only to obtain the actual twisted ground representation. "
                + "The oscillator algebra is the full native polynomial algebra P=MvPolynomial(Fin(D.rank) times N,C), "
                + "with no occupation cutoff and no positivity assumption. "
                + "groundRank and groundRepresentation choose the witnesses of actual_twisted_ground_representation D hu. "
                + "The ground module is the supplier's function space Ground(groundRank D hu), not an arbitrary substitute. "
                + "groundAction(a) is the actual representation of the quotient-group lift of (0,a). "
                + "Its invertibility follows from the group representation; it is not an added hypothesis.")),
            Paragraph(Text("Write q_a=B(a,a), s_a=2^(-q_a), C_a[k]=halfCreationCoeff D a k, and "
                + "Q_a(p)=halfTranslatedPolynomial D a p. The cover variable is t with physical z=t^2. "
                + "The cover prefactor is t^(-q_a). The coefficient at t^e on p tensor v is exactly "
                + "s_a times (sum_d coeff_d(Q_a(p)) C_a[e+q_a+d]) tensor groundAction(a)v. "
                + "The positive d offset arises because the native translation variable represents t^(-1), "
                + "not t. Q_a substitutes X(i,k)-B(a,e_i)x^(2k+1), with no spurious factor 2.")),
            Paragraph(Text("oscillatorTerm has support contained in the finite native Polynomial.support of Q_a(p). "
                + "The endomorphism oscillatorCoefficient uses a finsum whose finite support is proved for each input. "
                + "Additivity and scalar compatibility follow from native polynomial translation and finite-sum distribution. "
                + "chargedCoefficient is s_a times the tensor product of that actual endomorphism with groundAction(a). "
                + "charged_native_expansion identifies it with the finite Polynomial.support sum. "
                + "This is finiteness of the internal coefficient sum, not a claim that the entire Laurent series has finite support.")),
            Describe.Lean(
                DescribeId.Create("charged-term-support"),
                DeclarationHandle.Create(Prefix + "term_support"),
                H("Support of the exact native coefficient summand"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, LatticeParameter, Comma, Sp,
                    ChargeParameter, Comma, Sp, IntegerParameter("e"), Comma, Sp, PolynomialParameter,
                    Comma, Sp, Call("support", Call("oscillatorTerm", F.Id("D"), F.Id("a"), F.Id("e"), F.Id("p"))),
                    Subseteq, Call("support", Call("Q", F.Id("a"), F.Id("p")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every D:LatticeData, a:Charge(D), e:Integer and p:Oscillator(D), "
                    + "oscillatorTerm(D,a,e,p,d)=coeff_d(Q_a(p)) C_a[e+q_a+d]. A nonzero term requires "
                    + "a nonzero translated polynomial coefficient, so its function support is contained in Q_a(p).support. "
                    + "No determinant hypothesis is used. This support helper is consumed by charged_term_finite_support, "
                    + "charged_native_expansion and oscillatorCoefficient_as_sum; it is not a separate content advance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-term-finite-support"),
                DeclarationHandle.Create(Prefix + "charged_term_finite_support"),
                H("Finite internal coefficient sum on each polynomial"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, LatticeParameter, Comma, Sp,
                    ChargeParameter, Comma, Sp, IntegerParameter("e"), Comma, Sp, PolynomialParameter,
                    Comma, Sp, Call("HasFiniteSupport",
                        Call("oscillatorTerm", F.Id("D"), F.Id("a"), F.Id("e"), F.Id("p")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The complete parameter group is D:LatticeData, a:Charge(D), e:Integer "
                    + "and p:Oscillator(D), without hu. The finite native polynomial support and term_support "
                    + "give finite function support for the natural summation degree. This consumed helper justifies "
                    + "finsum additivity and scalar compatibility in oscillatorCoefficient. It imposes no occupation cutoff "
                    + "and says nothing about finiteness of support in the external Laurent exponent e."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-lower-bound"),
                DeclarationHandle.Create(Prefix + "charged_polynomial_lower_bound"),
                H("All-polynomial Laurent lower bound"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, GroundParameters, Comma, Sp,
                    ChargeParameter, Comma, Sp, PolynomialParameter, Comma, Sp, VectorParameter,
                    Comma, Sp, IntegerParameter("e"), Comma, Sp,
                    F.Id("e"), Lt, Seq(Minus, Call("q", F.Id("a")), Minus, Call("W", F.Id("p"))),
                    Implies, Call("A", F.Id("a"), F.Id("e"), Seq(F.Id("p"), F.Id("tensor"), F.Id("v"))), Eq, F.D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("W(p)=nativeOddWeightedDegree D p is the maximum native odd weight of a supported monomial, "
                        + "with W(0)=0. Every translated variable has polynomial degree at most its odd weight 2k+1. "
                        + "For each supported monomial, degree bounds for multiplication, powers and finite products "
                        + "give degree at most its weight. Taking the finite support supremum yields natDegree(Q_a(p))<=W(p). "
                        + "A supported translation index d therefore satisfies d<=W(p). If e<-q_a-W(p), "
                        + "then e+q_a+d<0 and the native creation coefficient is zero. Every summand vanishes.")),
                    Paragraph(Text("No homogeneity of p is required. The zero polynomial is covered by its empty support. "
                        + "At rank zero all oscillator polynomials are constants and W(p)=0. "
                        + "A negative q_a is allowed and simply moves the stated lower bound to positive cover exponent; "
                        + "q_a=0 leaves prefactor and scalar equal to one. No case changes the physical energy convention. "
                        + "Tensor induction gives a lower bound for every finite sum of simple tensors. "
                        + "chargedField is then a native HVertexOperator on the actual tensor carrier; no field truncation axiom is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-vacuum-coefficient"),
                DeclarationHandle.Create(Prefix + "charged_vacuum_coefficient"),
                H("Exact vacuum coefficient with the original normalization"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, GroundParameters, Comma, Sp,
                    ChargeParameter, Comma, Sp, IntegerParameter("e"), Comma, Sp, VectorParameter, Comma, Sp,
                    Call("A", F.Id("a"), F.Id("e"), Tensor(F.D(1), F.Id("v"))), Eq,
                    Call("s", F.Id("a")), Sp, Tensor(Call("C", F.Id("a"),
                        Seq(F.Id("e"), Plus, Call("q", F.Id("a")))), Call("groundAction", F.Id("a"), F.Id("v")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source telescope is D:LatticeData, hu:IsUnit(det(G(D))), "
                    + "a:Charge(D), e:Integer and v:ActualGround(D,hu), including the zero vector. "
                    + "Translation of the oscillator unit is the constant polynomial one, whose support is {0}. "
                    + "The coefficient is therefore exactly s_a times C_a[e+q_a] tensor groundAction(a)v. "
                    + "The scalar stays 2^(-B(a,a)); no factor, sign or exponent is absorbed into groundAction. "
                    + "This evaluation helper is consumed by charged_ground_leading."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-ground-leading"),
                DeclarationHandle.Create(Prefix + "charged_ground_leading"),
                H("Nonzero actual ground leading coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, GroundParameters, Comma, Sp,
                    ChargeParameter, Comma, Sp, VectorParameter, Comma, Sp, F.Id("v"), Neq, F.D(0), Implies,
                    Call("A", F.Id("a"), Seq(Minus, Call("q", F.Id("a"))), Seq(F.D(1), F.Id("tensor"), F.Id("v"))),
                    Neq, F.D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Native translation of one is one. Thus the complete vacuum coefficient formula is "
                        + "A_a[e](1 tensor v)=s_a C_a[e+q_a] tensor groundAction(a)v. "
                        + "The zero coefficient of the actual substituted exponential is one, by its zero constant logarithm "
                        + "and the native PowerSeries coefficient substitution theorem. At e=-q_a the coefficient is "
                        + "exactly s_a (1 tensor groundAction(a)v); every lower coefficient vanishes by the polynomial theorem.")),
                    Paragraph(Text("The scalar s_a is nonzero for every integer q_a. "
                        + "The monomial tensor-basis equivalence recovers groundAction(a)v as the coordinate at monomial zero "
                        + "of 1 tensor groundAction(a)v. If that tensor vanished, so would its coordinate. "
                        + "Applying the actual representation of the inverse quotient-group lift then gives v=0, "
                        + "contradicting precisely the stated nonzero-v hypothesis. "
                        + "This neither assumes a nonzero action nor reconstructs a duplicate projective representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-tensor-current-ward"),
                DeclarationHandle.Create(Prefix + "charged_tensor_current_ward"),
                H("Full integer-mode tensor current Ward identity"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, GroundParameters, Comma, Sp,
                    F.Id("i"), Colon, Call("Fin", Call("rank", F.Id("D"))), Comma, Sp,
                    ChargeParameter, Comma, Sp, IntegerParameter("m"), Comma, Sp, IntegerParameter("e"), Comma, Sp,
                    Call("J", F.Id("i"), F.Id("m")), Call("A", F.Id("a"), F.Id("e")), Minus,
                    Call("A", F.Id("a"), F.Id("e")), Call("J", F.Id("i"), F.Id("m")), Eq,
                    Call("B", Call("unitCharge", F.Id("D"), F.Id("i")), F.Id("a")), Sp,
                    Call("A", F.Id("a"), Seq(F.Id("e"), Minus, Open, F.D(2), F.Id("m"), Plus, F.D(1), Close))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every D:LatticeData, hu:IsUnit(det(G(D))), i:Fin(D.rank), "
                        + "a:Charge(D) and m,e:Integer, J_i[m] is tensorCurrent(D,ActualGround(D,hu),i,m). "
                        + "Multiplication in the formula is composition of endomorphisms on the full actual tensor carrier. "
                        + "The commutator is B(unitCharge(D,i),a) times A_a[e-(2m+1)]. Both m and e range over all integers, "
                        + "with the same shift on the creation and annihilation branches.")),
                    Paragraph(Text("For negative m, the native multiplication-current branch and the exact translated-variable "
                        + "identity give the positive odd-weight offset. For nonnegative m, the polynomial derivation "
                        + "commutes with translation and differentiates the actual creation coefficient; the frequency "
                        + "normalization cancels 2/(2m+1). The finite native coefficient map combines these two branches. "
                        + "Tensor-product extensionality then transports the oscillator commutator through the actual "
                        + "ground action and the original scalar. No current commutator or charged action law is assumed. "
                        + "This current covariance is distinct from energy covariance and charged-field pair locality."))),
                DescribeRole.Theorem),
            Paragraph(Text("The corrected all-state application in "),
                Ref("D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection"),
                Text(" uses this actual T_D and chargedField, with its original normalization and ground action. "
                + "Its state-field map Ytw is injective for every D and hu:IsUnit D.G.det. "
                + "The argument below uses the nonnegative current residue identity of the constructed fields; "
                + "kernel stability is a consequence, not a hypothesis, and source simplicity is not assumed.")),
            Paragraph(Text("Let K=ker(Ytw), and write J_i(n)=neutralMode D i n on the ordinary source. "
                + "For b in K, set B=vectorFrequencyBound D b, so J_i(n)b=0 for n>B by "),
                Ref("D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration"),
                Text(". For every d>=0, the actual nonnegative current residue equals "
                + "sum_{n=d}^B choose(1/2,n-d) I_(1+gamma)(Ytw(J_i(n)b))[[ell+d-n]]x. "
                + "Its other side is the ordinary d-th product of the actual current with I_gamma(Ytw(b)), "
                + "hence zero. Descending extraction in d removes the terms n>d; the diagonal coefficient is "
                + "choose(1/2,0)=1. Taking ell=0 and gamma=-e-3 reads native exponent e, for every integer e. "
                + "Thus Ytw(J_i(n)b)=0 for every n>=0, including the zero modes. The arbitrary integerization "
                + "label here tests all native coefficients and adds no parity premise on b.")),
            Paragraph(Text("Suppose K is nonzero and choose a nonzero b in it. The zero currents act diagonally: "
                + "(J_i(0)b)(a)=B(e_i,a)b(a). Form the finite-dimensional invariant envelope "
                + "V=span{[a,b(a)]:a in b.support} and T=K intersect V. The commuting zero currents restrict "
                + "to T. The simultaneous generalized-eigenspace theorem over C gives a nonzero common "
                + "generalized eigenvector there. On each nonzero charge coordinate its weights must equal "
                + "B(e_i,a); scalar cancellation in the generalized-eigenvector equations proves this directly. "
                + "Since the integral Gram matrix is invertible under hu, these weights separate charges. "
                + "The vector is therefore [a,p] with p nonzero. Only V and T are finite-dimensional; neither "
                + "the full carrier nor its charge sectors acquire that hypothesis.")),
            Paragraph(Text("In this sector put L={p:[a,p] in K}. Positive source modes give "
                + "J_i(k+1)[a,p]=(k+1)[a,sum_j G_ij partial_(j,k)p]. The scalar k+1 is nonzero over C. "
                + "Let H be the integral inverse Gram matrix mapped into C, so H gramComplex(D)=1. "
                + "Then partial_(j,k)p=sum_i H_ji (sum_l G_il partial_(l,k)p), which belongs to L by kernel "
                + "stability. The source mode normalization is k+1; it is not the target half-Fock frequency. "
                + "The existing actual current formulas in "), Ref("D5/S3/VertexAlgebra/LatticeSugawaraCurrents"),
                Text(" supply the weighted derivatives, and the minimum-degree and zero-partial rigidity "
                + "results of "), Ref("D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity"),
                Text(" apply to L without any finite-dimensionality assumption. A nonzero element of least "
                + "total degree has every partial zero, hence is a nonzero constant. Rescaling shows [a,1] in K.")),
            Paragraph(Text("Take the actual ground vector g(t)=1. It is nonzero by evaluation at t=0, "
                + "including when D.rank=0. Since Ytw([a,1])=chargedField(a), its coefficient at "
                + "e=-B(a,a) on 1 tensor g is exactly 2^(-B(a,a)) (1 tensor groundAction(a)g). "
                + "charged_ground_leading makes this nonzero: the scalar is nonzero, the actual group action "
                + "is invertible, and the tensor coordinate at the unit monomial detects the ground vector. "
                + "This contradicts [a,1] in K, so K=0 and Ytw is injective. The argument uses no arbitrary "
                + "Nontrivial parameter, positive rank, positive norm, positivity or unitary structure. "
                + "Indefinite unimodular forms are included; singular Gram matrices are outside this "
                + "faithfulness telescope, even though their finite Corr construction is defined.")),
            Paragraph(Text("Faithfulness here means that equality of all native endomorphism coefficients "
                + "of Ytw(u) and Ytw(w) forces u=w. It is not surjectivity onto all Laurent fields, "
                + "simplicity of a completed VOA, positive-energy grading or a physical realization. "
                + "This combines the classical twisted ground coefficient with current residues and ordinary "
                + "polynomial rigidity; it makes no literature-novelty claim.")),
            Paragraph(Text("The native universal half_creation_coefficient_transport is the exact source for "
                + "charged coefficient products: translating C_b[n] gives kappa_g(d) C_b[n-d], "
                + "where kappa_g is the coefficient of ((1-s)/(1+s))^g and g=B(a,b). "
                + "Both cover branches must be retained. Their pole bounds are p=max(0,-g), q=max(0,g), "
                + "and the physical two-step order is abs(g); positive g can have an opposite-cover pole. "
                + "This coefficient transport statement alone supplies no one-sided delta identity, "
                + "pair-locality or twisted Jacobi conclusion.")),
            Paragraph(Text("The original charged energy-covariance theorem is proved in "),
                Ref("D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero"),
                Text(". For every D, hu:IsUnit D.G.det, charge a, integer e and v:ActualTensor D hu, "
                + "the original commutator L0(A_a[e]v)-A_a[e](L0(v)) equals ((e+B(a,a))/2) A_a[e]v. "
                + "L0 uses the integral inverse Gram matrix mapped into C; both inverse laws follow from hu. "
                + "Weighted substitution gives signed translated coefficient weight N-d, and the original "
                + "creation index e+q_a+d gives total weight N+e+q_a. Existing finite support and the actual "
                + "L_zero_monomial_coeff then give the full polynomial and tensor statement, including the "
                + "former C_b[n] termwise application. Negative creation indices give literal zero. "
                + "The scalar 2^(-q_a), original groundAction, ground shift D.rank/16 and physical z=t^2 "
                + "are retained. Rank zero and indefinite Gram data are included; no metric or positivity is assumed. "
                + "Full conformal twisted-module structure and the further VOA/CFT programme still require additional identities.")),
            Paragraph(Text("The precise termwise native cover-energy application follows from the proved L0 derivation. "
                + "For H satisfying BOTH H*gramComplex(D)=1 and gramComplex(D)*H=1, use the actual half-Fock L0. "
                + "If the input polynomial is C_b[n], the degree-d summand is "
                + "T_d=kappa_g(d) C_b[n-d] C_a[e+q_a+d]. Universal transport gives this equality from the actual translation, "
                + "not from an assumed field commutator. The native creation coefficient grading makes the two nonzero factors "
                + "homogeneous of weights (n-d).toNat and (e+q_a+d).toNat. If either integer index is negative the term is zero. "
                + "Otherwise their sum of weights is n+e+q_a. The exact termwise identity is "
                + "L0(T_d)=(D.rank/16+(n+e+q_a)/2) T_d, for all integer n and e, using "
                + "the actual L_zero_monomial_coeff supplier and finite monomial decomposition. "
                + "Weighted substitution and L_zero_monomial_coeff give this termwise identity under the two stated inverse-Gram hypotheses. "
                + "The ground shift remains D.rank/16 and physical z=t^2. Lifting the termwise identity to a complete "
                + "charged tensor coefficient covariance is supplied below by the native coherent-seed proof.")),
            Describe.Lean(
                DescribeId.Create("charged-tensor-virasoro-ward"),
                DeclarationHandle.Create(Prefix + "charged_tensor_virasoro_ward"),
                H("All integer Virasoro modes on every actual tensor state"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, GroundParameters, Comma, Sp,
                    ChargeParameter, Comma, Sp, IntegerParameter("m"), Comma, Sp,
                    IntegerParameter("e"), Comma, Sp, F.Id("v"), Colon,
                    Call("ActualTensor", F.Id("D"), F.Id("hu")), Comma, Sp,
                    Call("L", F.Id("m"), Call("A", F.Id("a"), F.Id("e"), F.Id("v"))), Minus,
                    Call("A", F.Id("a"), F.Id("e"), Call("L", F.Id("m"), F.Id("v"))), Eq,
                    Call("k", F.Id("a"), F.Id("m"), F.Id("e")), Sp,
                    Call("A", F.Id("a"), Seq(F.Id("e"), Minus, F.D(2), F.Id("m")), F.Id("v"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Here H=(G(D) inverse).map(Int.castRingHom C), L_m is exactly "
                        + "tensorL(D,ActualGround(D,hu),H,m), and A_a[e] is the original chargedCoefficient. "
                        + "The scalar is k(a,m,e)=(e-2m+(m+1)B(a,a))/2, with the integer numerator cast to C. "
                        + "The telescope contains every D:LatticeData, hu:IsUnit(det(G)), a:Charge(D), "
                        + "m,e:Integer and v:ActualTensor(D,hu). There is no positivity, positive-rank, signature, "
                        + "homogeneity, occupation cutoff or additional inverse premise. Both inverse identities "
                        + "are obtained locally from hu. The cover remains t with physical z=t^2; "
                        + "q=B(a,a), s_a=2^(-q) and the actual groundAction are unchanged.")),
                    Paragraph(Text("Put F_d=halfCreationCoeff(a,d), A_n=sum_i a_i X(i,n), w_n=2n+1. "
                        + "Coefficient extraction from exponential_derivative and series_derivative_coeff gives "
                        + "sum_n A_n F_(R-w_n)=(R/2)F_R for every signed R; only finitely many terms survive. "
                        + "The normal action is split into its two mixed regions, its positive double-contraction "
                        + "interval and its genuine negative vacuum quadratic. The two inverse Gram contractions "
                        + "identify the mixed terms, and their sum is the creation recurrence with its low terms removed. "
                        + "All normal sums are finite on each polynomial, as supplied by normalPair_finite; "
                        + "no finite endomorphism support or convergence hypothesis is introduced.")),
                    Paragraph(Text("The native coherent seeds use precisely m=1,-1,2,-2. For m=-N, N=1,2, "
                        + "write Q_N=rawL_(-N)1. Actual translation gives O_(d-q)Q_N=Q_N F_d "
                        + "minus sum_(n<N) A_n F_(d+2N-w_n) plus (Nq/2)F_(d+2N). "
                        + "Thus subtracting O_(d-q)Q_N completes the recurrence and proves "
                        + "rawL_m F_d-O_(d-q)(rawL_m1)=((d-2m+mq)/2)F_(d-2m). "
                        + "Every signed d is included. At d=-2N the input creation coefficient vanishes "
                        + "but the translated quadratic contributes Nq/2 times F_0, so the residual is -Nq/2. "
                        + "This branch is retained rather than replacing d by d.toNat.")),
                    Paragraph(Text("For each seed mode form R_e=[L_m,O_e]-k(a,m,e)O_(e-2m). "
                        + "The existing oscillator current Ward identity and L_current_commutator imply "
                        + "[J_i(j),R_e]=B(e_i,a)R_(e-(2j+1)); the scalar cancellation is "
                        + "k(a,m,e)-k(a,m,e-(2j+1))=j+1/2. Polynomial generation then uses the predicate "
                        + "for every e, R_e(p)=0, so multiplication by a variable has the required shifted "
                        + "induction hypothesis. This proves each generator mode on arbitrary nonhomogeneous polynomials.")),
                    Paragraph(Text("The imported exact L_virasoro identity and commutator Jacobi close the modes: "
                        + "the bracket of modes r,s yields r+s whenever r differs from s, since "
                        + "k(a,s,e)k(a,r,e-2s)-k(a,r,e)k(a,s,e-2r)=(r-s)k(a,r+s,e). "
                        + "Its central scalar identity commutes. Modes 1,-1 give zero; induction from 2 with 1 "
                        + "and from -2 with -1 gives every remaining integer. Tensor extensionality carries "
                        + "this full oscillator theorem through the literal scalar and actual ground action. "
                        + "The rank/16 ground energy therefore cancels and is absent from the charged primary weight."))),
                DescribeRole.Theorem),
            Paragraph(Text("The all-mode theorem proves conformal covariance of the original charged generator on every target state. "
                + "A full conformal twisted-module structure for all corrected source states still requires further identities. "
                + "The actual native spectrum keeps ground shift D.rank/16 and variable z=t^2. "
                + "Leech realization, orbifold extension, Monster symmetry, full VOA and CFT, anomalies, fusion, "
                + "string theory and AdS/CFT remain open. The classical construction and these native supplier applications "
                + "carry no literature-novelty claim.")))));
}
