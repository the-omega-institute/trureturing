using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeSugawaraConformalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeSugawaraConformal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual matrix Sugawara coefficients satisfy Virasoro and generate charge-sensitive translation.",
        H("Actual All-Charge Matrix Sugawara Modes"),
        Blocks(
            Paragraph(Text("The actual quadratic field is one half the finite double sum "
                + "of H(i,j) times normalMinusOne(neutralField(i),neutralField(j)). "
                + "Its mode L(m) is the normalized coefficient at m+1. Let Gc be the "
                + "complex cast of the integral Gram matrix and assume H Gc=Gc H=1. "
                + "These are the only additional hypotheses for the conformal laws; "
                + "the rank may be zero and every integral charge is included.")),
            Paragraph(Text("For a polynomial p, R is the largest frequency j+1 among "
                + "the variables X(i,j) occurring in p, or zero when p is constant. "
                + "For a finite-charge vector v, take the maximum over its sector "
                + "support. Positive currents above R kill v. The normal summand "
                + "N(i,j;k,m-k)v is supported in [min(0,m-R),R]. Each input, "
                + "including each intermediate current image, has its own bound.")),
            Describe.Lean(
                DescribeId.Create("lattice-current-heisenberg"),
                DeclarationHandle.Create(Prefix + "neutralMode_heisenberg"),
                H("Actual Heisenberg law in every charge sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all integers m,n and all lattice indices i,j, "
                    + "[h_i(m),h_j(n)]=m G(i,j) delta(m+n,0) id. Multiplication and "
                    + "Gram-weighted partial differentiation prove both mixed sign "
                    + "branches; zero currents are the actual charge scalars."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-sugawara-coefficient-sum"),
                DeclarationHandle.Create(Prefix + "sugawaraMode_interval_sum"),
                H("The normal-product coefficient equals the statewise finite sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("At coefficient m+1 the defining subtype equation "
                    + "has terms h_i(-t-1)h_j(m+t+1) and h_j(m-t)h_i(t). "
                    + "Reindexing the two natural sums gives respectively k<0 and "
                    + "k>=0, with N(i,j;k,l)=h_i(k)h_j(l) in the first half and "
                    + "h_j(l)h_i(k) in the second. Thus L(m)v is one half the "
                    + "H-weighted double sum of N(i,j;k,m-k)v over the stated finite "
                    + "interval. This is finite support on v, not on endomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-lattice-virasoro"),
                DeclarationHandle.Create(Prefix + "sugawaraMode_virasoro"),
                H("All-integer Virasoro with central charge equal to rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every pair of integers m,n, the actual "
                        + "endomorphisms satisfy [L(m),L(n)]=(m-n)L(m+n) plus "
                        + "rank(D)(m^3-m)/12 times delta(m+n,0) id. The current law "
                        + "gives [L(m),h_i(q)]=-q h_i(m+q). The central defect commutes "
                        + "with all currents and is scalar independently on each "
                        + "charge sector. Weighted Euler kills the off-diagonal defect.")),
                    Paragraph(Text("For a>0, evaluating L(a)L(-a) on single(beta,1) "
                        + "keeps both charged boundary terms. Subtracting 2a L(0) "
                        + "cancels their charge contribution. The remaining inverse-Gram "
                        + "trace is rank(D), and the oscillator sum is (a^3-a)/6. "
                        + "Skew symmetry supplies negative diagonal modes and the "
                        + "zero diagonal is zero. Consequently the scalar is the "
                        + "same on every integral charge sector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-lattice-zero-mode"),
                DeclarationHandle.Create(Prefix + "sugawaraMode_zero_single"),
                H("Zero mode equals frequency Euler plus the lattice norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("On single(beta,p), L(0) is the oscillator "
                    + "frequency Euler derivation plus B(beta,beta)/2 times p. "
                    + "The inverse-Gram quadratic charge scalar equals this original "
                    + "lattice norm. The identity holds for every polynomial p. "
                    + "For an oscillator polynomial homogeneous of frequency degree r, "
                    + "the same mode acts by r+B(beta,beta)/2. This follows from the "
                    + "actual Euler derivation and is included in the generator contract."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-lattice-conformal-generators"),
                DeclarationHandle.Create(Prefix + "actual_conformal_generators"),
                H("The Virasoro minus-one mode translates the genuine lattice generators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The actual coefficient L(-1) equals T on all "
                    + "finite-charge vectors. On each charged ground state its value "
                    + "is single(beta,B_beta); its current commutators then determine "
                    + "its action on every oscillator polynomial. The contract combines "
                    + "the full Virasoro law and zero-mode formula with the actual T formula, vacuum "
                    + "annihilation, charged actualField covariance and neutral-current "
                    + "covariance, all for the same actual carrier and coefficients."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, "
                + "arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), "
                + "gives the classical charged generators, translation and conformal "
                + "construction. The finite normal-ordering and commutator architecture "
                + "also follows Kalle Kytola's Apache-2.0 Sugawara.lean at revision "
                + "5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The polynomial Fock "
                + "carrier is not used to transfer these lattice identities.")),
            Paragraph(Text("These are conformal mode and generator identities. "
                + "All-state field reconstruction and its vertex-algebra axioms remain "
                + "separate obligations. Positive energy and finite-dimensional weight "
                + "spaces require further lattice hypotheses and are not asserted.")),
            Paragraph(Text("Let D be any existing LatticeData: its rank is any natural "
                + "number, its Gram matrix G is integral and symmetric, and its diagonal "
                + "is even. Write L for the integral charge group Fin(rank) to Z, P for "
                + "the complex polynomial algebra on variables X(i,j), and V for the "
                + "finite-support functions L to P. The translation construction itself "
                + "uses no positivity, nondegeneracy, unimodularity or positive-rank "
                + "hypothesis. The Sugawara laws use the inverse-Gram hypotheses above.")),
            Paragraph(Text("The actual polynomial derivation D_osc sends X(i,j) to "
                + "(j+1) X(i,j+1) and kills constants. Put B_beta=sum_i beta_i X(i,0). "
                + "The endomorphism T sends single(beta,p) to "
                + "single(beta,D_osc(p)+B_beta p), extending linearly over finite "
                + "charge support. The vacuum single(0,1) is killed by T. "
                + "In particular the multiplication term uses the charge of the "
                + "sector on which T acts.")),
            Describe.Lean(
                DescribeId.Create("actual-lattice-translation-covariance"),
                DeclarationHandle.Create(Prefix + "actual_lattice_translation_covariance"),
                H("The actual charged lattice fields satisfy translation covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every D, charge alpha and integer ordinary mode n, "
                        + "[T,Y_alpha[n]]=-n Y_alpha[n-1], as an equality of complex "
                        + "endomorphisms of V. The field is the existing actualField, "
                        + "with its lower-triangular cocycle, actual creation exponential "
                        + "and annihilation substitution. Arbitrary input charges and "
                        + "arbitrary oscillator polynomials remain quantified.")),
                    Paragraph(Text("The raw coefficient theorem rawCoeff_translation "
                        + "proves [T,R_alpha(k)]=(k+1) R_alpha(k+1) for every integer "
                        + "exponent k. Ordinary modes are obtained from the actual "
                        + "field constructor by k=-n-1. This distinguishes the exponent "
                        + "and ordinary-mode shifts.")),
                    Paragraph(Text("Coefficientwise oscillator derivation of the actual "
                        + "creation exponential is E'_alpha-B_alpha E_alpha. The proof "
                        + "uses its formal differential equation, coefficientwise "
                        + "Leibniz and zero constant term for the difference. Strong "
                        + "induction on the finite antidiagonal recurrence kills that "
                        + "difference. Thus D_osc C_t=(t+1) C_(t+1)-B_alpha C_t. "
                        + "For t=-1 the multiplier is zero, and for t<-1 both "
                        + "creation coefficients vanish; these integer cases are explicit.")),
                    Paragraph(Text("Let Q_alpha(p;u) be the existing annihilation "
                        + "substitution X(i,j) to X(i,j)-B(alpha,e_i)u^(j+1). "
                        + "Polynomial induction proves Q_alpha(D_osc p)= "
                        + "D_osc Q_alpha(p)+u^2 partial_u Q_alpha(p) for every p. "
                        + "The charge transport is Q_alpha(B_beta)= "
                        + "B_beta-B(alpha,beta)u, and B_(alpha+beta)=B_alpha+B_beta.")),
                    Paragraph(Text("A finite coefficient convolution applied to each "
                        + "polynomial separately includes its whole support. Its "
                        + "linearity uses zero coefficients outside the finite support; "
                        + "it imposes no bound from p on D_osc p or B_beta p. "
                        + "Monomial induction gives the reindexing d to d+1, including "
                        + "the zero derivative boundary. For b=B(alpha,beta) the "
                        + "annihilation term contributes -d, the changed charge "
                        + "contributes b, and the creation derivative contributes "
                        + "k-b+d+1. Their sum is k+1. This cancellation proves "
                        + "covariance on the actual carrier; a fixed-charge Fock operator "
                        + "cannot supply it.")),
                    Paragraph(Text("The arbitrary-polynomial coefficient identity "
                        + "actual_creation_coefficient_transport identifies rawCoeff on every "
                        + "single(beta,p) with the prescribed rawSingle formula. "
                        + "The same cocycle scalar factors from both compositions. "
                        + "Extensionality on finitely supported charge functions "
                        + "extends the result to every actual carrier vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-translation-generators"),
                DeclarationHandle.Create(Prefix + "actual_translation_generators"),
                H("The vacuum and both generating families share the constructed translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every D, the conjunction records the action "
                    + "on every single(beta,p), the zero vacuum action, all charged "
                    + "ordinary-mode commutators and all neutral-mode commutators. "
                    + "All statements concern the same actual T and V; "
                    + "the conjunction makes no all-state reconstruction claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("neutral-lattice-translation-covariance"),
                DeclarationHandle.Create(Prefix + "neutral_translation_covariance"),
                H("Every actual neutral current mode has the matching covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every i in Fin(rank) and every integer m, "
                        + "[T,neutralMode(i,m)]=-m neutralMode(i,m-1), on all of V. "
                        + "Negative modes use the oscillator derivation of the "
                        + "multiplication variable. The zero mode is a scalar on "
                        + "each charge sector. Positive modes use the commutator "
                        + "of D_osc with polynomial partial derivatives. At m=1 "
                        + "the oscillator contribution is zero and differentiation "
                        + "of B_beta supplies exactly the zero-mode charge scalar. "
                        + "For m>1 the charge derivative vanishes and the oscillator "
                        + "commutator supplies the lower positive mode.")),
                    Paragraph(Text("Bakalov-Kac, Twisted Modules over Lattice Vertex "
                        + "Algebras, arXiv math/0402315v1, section 4.1, printed "
                        + "pages 8-9, equation (4.15), specifies the translation "
                        + "operator through the neutral commutator and charged "
                        + "ground-state action. Equation (4.12) supplies the lattice "
                        + "generator formula. This formalization verifies those "
                        + "generator translation identities on the existing actual "
                        + "polynomial and all-charge carrier. The degenerate and "
                        + "indefinite cases use no inverse Gram matrix.")),
                    Paragraph(Text("These covariance laws supply the input required by "
                        + "the carrier-generic normalMinusOne_translation theorem "
                        + "and by a future all-charge state-field construction. "
                        + "They do not supply an all-state vertex algebra or "
                        + "Jacobi, the Monster realization, Moonshine, "
                        + "CFT, string theory or an AdS/CFT bridge."))),
                DescribeRole.Theorem))));
}
