using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula Creation(Formula charge, Formula degree) => Call("C", charge, degree);
    private static Formula Degree => F.Id("n");
    private static Formula TranslationDegree => F.Id("d");
    private static Formula Right => F.Id("b");
    private static Formula Left => F.Id("a");
    private static Formula Axis => F.Id("i");
    private static Formula Mode => F.Id("k");
    private static Formula Frequency => Seq(F.D(2), Mode, Plus, F.D(1));
    private static Formula Exponential => Call("E", Right);
    private static Formula Series => Call("S", Right);
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual odd-weight exponential coefficients and their two-factor contraction",
        H("Native Half-Fock Creation Transport"),
        Blocks(
            Paragraph(Text("D has arbitrary natural rank, an integral symmetric Gram matrix and even diagonal. "
                + "No positivity, unimodularity, inverse Gram matrix, rank 24 or locality is assumed. "
                + "The oscillator carrier remains the infinite algebra P=MvPolynomial(Fin(D.rank) times N,C). "
                + "Each individual polynomial has finite support; the carrier has no occupation cutoff. "
                + "A variable X(i,k) has cover weight omega(i,k)=2k+1.")),
            Paragraph(Text("For charge b, the actual halfCreationSeries S_b has zero even coefficients. "
                + "Its coefficient at 2k+1 is 2/(2k+1) times sum_i b_i X(i,k). "
                + "halfCreationExponential is the native PowerSeries.exp(P) substituted in this zero-constant series. "
                + "Write C_b[n]=0 for negative integer n and otherwise take its n.toNat coefficient. "
                + "The finite polynomial translation Q_a:P->P[x] substitutes "
                + "X(i,k)->X(i,k)-B(a,e_i)x^(2k+1). There is no additional factor 2 in this shift.")),
            Describe.Lean(
                DescribeId.Create("exponential-derivative"),
                DeclarationHandle.Create(Prefix + "exponential_derivative"),
                H("Native formal exponential differential equation"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Right, Comma, Sp,
                    Call("derivative", Exponential), Eq,
                    Exponential, Sp, Call("derivative", Series)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("E_b is halfCreationExponential and S_b is halfCreationSeries. "
                    + "The zero constant coefficient of S_b makes formal substitution admissible. "
                    + "The power-series chain rule and derivative of exp give E_b'=E_b S_b'. "
                    + "This is a directly reused formal-series identity, consumed in the grading "
                    + "induction, transport differential equations and annihilation chain rule."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exponential-constant"),
                DeclarationHandle.Create(Prefix + "exponential_constant"),
                H("Native exponential initial coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Right, Comma, Sp,
                    Call("coeff", F.D(0), Exponential), Eq, F.D(1)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Only the zeroth summand contributes to the constant coefficient "
                    + "of exp(S_b), because S_b has constant coefficient zero. This initial value "
                    + "is consumed by the grading induction, uniqueness in transport and the "
                    + "zero-initial-residual argument for annihilation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("series-derivative-coeff"),
                DeclarationHandle.Create(Prefix + "series_derivative_coeff"),
                H("Parity and normalization of the logarithmic derivative"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Right, Comma,
                    Degree, InMacro, Naturals, Comma, Sp,
                    Call("coeff", Degree, Call("derivative", Series)), Eq,
                    Call("T", Right, Degree)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("T_b(n) denotes 2 sum_i b_i X(i,n/2) for even n, and zero "
                    + "for odd n. Formal differentiation multiplies the coefficient at n+1 by n+1; "
                    + "this cancels its denominator when n is even. For odd n the source "
                    + "coefficient vanishes. The formula includes n=0, zero charge and rank zero. "
                    + "Both grading and transport consume this exact parity formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-creation-coefficient-grading"),
                DeclarationHandle.Create(Prefix + "half_creation_coefficient_grading"),
                H("Actual odd-weight grading"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Right, Comma, Sp,
                    Degree, InMacro, Integers, Comma, Sp,
                    Call("Hom", F.Id("omega"), Creation(Right, Degree), Call("toNat", Degree))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Differentiating the actual exponential gives a finite antidiagonal recurrence. "
                    + "The coefficient at derivative index m of S_b' is 2 sum_i b_i X(i,m/2) if m is even, "
                    + "and zero otherwise. Strong induction proves that C_b[n] has omega-weight n for n>=0. "
                    + "The negative-index coefficient is zero and is homogeneous in its stated truncated degree. "
                    + "This grading is consumed by the transport theorem: evaluation of each supported monomial "
                    + "has polynomial degree at most its omega-weight, so coefficients of Q_a(C_b[n]) above n vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-creation-coefficient-transport"),
                DeclarationHandle.Create(Prefix + "half_creation_coefficient_transport"),
                H("Universal integer-index coefficient transport"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Left, Comma, Right, Comma,
                    Degree, InMacro, Integers, Comma, TranslationDegree, InMacro, Naturals, Comma, Sp,
                    Call("coeff", TranslationDegree, Call("Q", Left, Creation(Right, Degree))), Eq,
                    Call("kappa", Call("B", Left, Right), TranslationDegree), Sp,
                    Creation(Right, Seq(Degree, Minus, TranslationDegree))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Define halfContraction K_g as rescale(-1)(binomialSeries(C,g)) "
                        + "times binomialSeries(C,-g), with parameter ring explicitly Z and g=B(a,b). "
                        + "The native convention is binomialSeries(g)=(1+s)^g; hence "
                        + "K_g(s)=((1-s)/(1+s))^g, interpreted as a formal series at s=0. "
                        + "kappa_g(d) is its actual d-th coefficient, not an assumed BCH factor.")),
                    Paragraph(Text("Map the creation series and its exponential into P[x] by the actual translation. "
                        + "The translated logarithmic derivative differs from the coefficient embedding by "
                        + "-2g*x^(m+1) at even m and zero at odd m. Multiplication by 1-x^2*u^2 "
                        + "therefore gives -2g*x. The integer descending-Pochhammer recurrence proves "
                        + "the exact derivative identity for each rescaled binomial factor. The product satisfies "
                        + "(1-x^2*u^2)K_g(xu)'=-2g*x*K_g(xu). The denominator is a unit. "
                        + "The translated exponential and the embedded exponential times K_g(xu) consequently "
                        + "satisfy the same first-order formal recurrence and have constant coefficient 1. "
                        + "Strong-induction uniqueness identifies them. Finite coefficient convolution "
                        + "and polynomial coefficient extraction give the stated universal law.")),
                    Paragraph(Text("The negative source index gives zero on both sides. For n>=0 and d>n, "
                        + "the actual weighted-degree bound proves the left side zero and the negative-index "
                        + "creation convention proves the right side zero. All coefficient sums are finite "
                        + "in their selected degree; no convergence premise or operator BCH axiom enters.")),
                    Paragraph(Text("This is classical half-lattice mathematics with zero novelty. The literature "
                        + "anchor is the reflection-twisted lattice construction of Frenkel-Lepowsky-Meurman "
                        + "and the lattice-module account in Bakalov-Kac. The argument here uses the "
                        + "native formal exponential, finite polynomial translation and integer binomial series.")),
                    Paragraph(Text("The charged oscillator coefficient uses the finite support of Q_a(p): "
                        + "2^(-q_a) times sum_d Q_a(p)[d] C_a[e+q_a+d], with q_a=B(a,a) and integer zpow. "
                        + "The cover prefactor is t^(-q_a); the physical coordinate is z=t^2. "
                        + "The ground operator must come from actual_twisted_ground_representation D hu "
                        + "and its representation multiplication and central sign, not an assumed action. "
                        + "Transport supplies the constant-input step of the ordered-product expansion; "
                        + "grading supplies the creation-energy calculation. These applications require "
                        + "their own field support, ground action and conformal-operator arguments.")),
                    Paragraph(Text("Both cover branches are mandatory: for positive g the pole is at t=-u, "
                        + "and for negative g it is at t=u. The scalar denominator exponents are "
                        + "p=max(0,-g) and q=max(0,g), with p+q=abs(g). Passing to a locality "
                        + "statement in z=t^2 requires the actual operator product identity. "
                        + "No one-sided native delta locality bound is asserted. The original untwisted "
                        + "locality theorem uses its own normalization. These coefficient identities do not establish twisted Jacobi, "
                        + "the all-state twisted module, orbifold, Leech specialization, Monster action, "
                        + "full CFT, string theory or AdS/CFT."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-annihilation-creation"),
                DeclarationHandle.Create(Prefix + "half_annihilation_creation"),
                H("Actual annihilation on integer creation coefficients"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Axis, Comma,
                    Mode, InMacro, Naturals, Comma, Right, Comma, Degree, InMacro, Integers, Comma, Sp,
                    Call("A", Axis, Mode, Creation(Right, Degree)), Eq,
                    Call("lambda", Axis, Mode, Right), Sp,
                    Creation(Right, Seq(Degree, Minus, Grp(Frequency)))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Here i ranges over Fin(D.rank), k over every natural mode, "
                        + "b over every integral charge and n over every integer. A(i,k) is the actual "
                        + "Gram-weighted annihilation derivation, and lambda(i,k,b)="
                        + "(2/(2k+1))*B(e_i,b). There is no inverse Gram matrix or nonzero-charge premise.")),
                    Paragraph(Text("Coefficientwise derivation commutes with the formal series derivative. "
                        + "Applying A(i,k) coefficientwise to E_b and subtracting E_b A(i,k)S_b "
                        + "gives a residual satisfying a homogeneous first-order formal differential equation "
                        + "with initial coefficient zero. Formal coefficient uniqueness makes this "
                        + "residual zero. Annihilation of S_b is the single monomial "
                        + "lambda(i,k,b)*u^(2k+1), giving the coefficient shift. Negative source "
                        + "indices and negative shifted indices retain their zero convention. "
                        + "The charged tensor coefficient current law consumes this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-translated-derivation"),
                DeclarationHandle.Create(Prefix + "half_translated_derivation"),
                H("Annihilation commutes with finite polynomial translation"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Axis, Comma,
                    Mode, InMacro, Naturals, Comma, Right, Comma, F.Id("p"), Comma, Sp,
                    Call("Q", Right, Call("A", Axis, Mode, F.Id("p"))), Eq,
                    Call("Apoly", Axis, Mode, Call("Q", Right, F.Id("p")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The parameters have the same unrestricted lattice, colour, "
                    + "mode and charge ranges as above, and p is an arbitrary oscillator polynomial. "
                    + "Apoly acts coefficientwise on P[x]; it does not differentiate the cover variable x. "
                    + "The translation of each generator is X(i,k) minus a scalar monomial in x, "
                    + "which coefficientwise annihilation kills. The variable law extends to every "
                    + "polynomial by addition and Leibniz induction. This commutation is consumed "
                    + "with the creation identity in the charged oscillator current Ward calculation."))),
                DescribeRole.Theorem))));
}
