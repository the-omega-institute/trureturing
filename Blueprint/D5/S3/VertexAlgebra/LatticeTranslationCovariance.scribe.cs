using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeTranslationCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeTranslationCovariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charge-sensitive translation is covariant with every actual lattice generator.",
        H("Actual All-Charge Lattice Translation"),
        Blocks(
            Paragraph(Text("Let D be any existing LatticeData: its rank is any natural "
                + "number, its Gram matrix G is integral and symmetric, and its diagonal "
                + "is even. Write L for the integral charge group Fin(rank) to Z, P for "
                + "the complex polynomial algebra on variables X(i,j), and V for the "
                + "finite-support functions L to P. There is no positivity, "
                + "nondegeneracy, unimodularity or positive-rank hypothesis.")),
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
                        + "They do not prove generator locality, an all-state "
                        + "vertex algebra or Jacobi, a conformal vector, Moonshine, "
                        + "CFT, string theory or an AdS/CFT bridge."))),
                DescribeRole.Theorem))));
}
