using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class SymmetricSpectrumEndAmplitudeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/escobar2025earlystateexclusion");

    private static readonly LibraryNoteRef Fusion =
        LibraryNoteRef.Create("D5/L/GraphInvariants/escobar2026spectralfusion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let a chain of seven sites with positive couplings, real potentials and a spectrum closed under negation have perfect state transfer between its end sites at a time T. Then its eigenvalues are 0, x, -x, y, -y, z, -z with 0 < x < y < z, exp(iTx) = -1, exp(iTy) = 1, exp(iTz) = -1, and its first-site amplitude at the time tau is P (1/(x^2 y^2 z^2) + cos(tau x)/(x^2 (y^2 - x^2)(z^2 - x^2)) + cos(tau y)/(y^2 (y^2 - x^2)(z^2 - y^2)) + cos(tau z)/(z^2 (z^2 - x^2)(z^2 - y^2))), P being the product of the couplings. For T > 0 this gives natural numbers a < b < c, with a and c odd and b even, such that the spectrum is (pi/T)(0, a, -a, b, -b, c, -c), the amplitude is a positive multiple of the cosine sum N(a, b, c; pi tau / T) of Escobar, Garcia and Minenkova (arXiv:2507.18767), and the chain has perfect state transfer at the time T/g for every common divisor g of a, b, c.",
        H("Spectrum and first-site amplitude of seven-site transfer chains with symmetric spectrum"),
        Blocks(
            Node("amplitude", "The first-site amplitude in the positive eigenvalues", AmplitudeFormula(),
                Paragraph(Text("Here pathHamiltonian(r, q) is the Hamiltonian H of the path on the seven sites 0, ..., 6 with the couplings r on its six edges and the potentials q on its sites; eigenvalues(H, k) is the k-th eigenvalue lambda_k of the Hermitian matrix H in Mathlib's enumeration, with orthonormal eigenvectors W(., k); HasPST(H, T, 0, last(6)) says that the entry of exp(i T H) between the sites 0 and 6 has modulus one; hamiltonianPropagator(H, tau, 0, 0) is the entry of exp(-i tau H) at the first site; Perm(Fin 7) is the set of permutations of the seven indices; ![...] is the vector with the listed entries; I is the imaginary unit and (v : C) the complex number equal to the real number v. Write P for the product of the six couplings. The entries of H^p between the two end sites vanish for p < 6 and equal P for p = 6, so the spectral weights under perfect state transfer, "),
                    Ref("D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_spectral_weights"),
                    Text(", give that the eigenvalues are simple and, with rho_k = P / prod_{l != k} (lambda_k - lambda_l) and gamma = exp(i T H)(0, 6), that exp(i T lambda_k) rho_k = gamma |W(0, k)|^2 and |rho_k| = |W(0, k)|^2. Seven distinct real numbers closed under negation are, in increasing order mu_0 < ... < mu_6, the numbers -z, -y, -x, 0, x, y, z with 0 < x < y < z: the map i -> -mu_(6 - i) is strictly increasing with the same range, and a strictly increasing enumeration of a finite set is unique. The permutation sigma sorts the eigenvalues. The products prod_{j != i} (mu_i - mu_j) are 2 z^2 (z^2 - x^2)(z^2 - y^2) at -z and z, -2 y^2 (y^2 - x^2)(z^2 - y^2) at -y and y, 2 x^2 (y^2 - x^2)(z^2 - x^2) at -x and x, and -x^2 y^2 z^2 at 0. Since P > 0, rho is negative at the eigenvalue 0, so 1 = exp(i T 0) = -gamma; with gamma = -1 the signs of rho at x, y, z give exp(i T x) = -1, exp(i T y) = 1 and exp(i T z) = -1. Finally exp(-i tau H)(0, 0) = sum_k |W(0, k)|^2 exp(-i tau lambda_k) with |W(0, k)|^2 = P / |prod_{l != k} (lambda_k - lambda_l)|, and adding the terms at mu and -mu gives the cosines. The statement holds for every real T. The formula is Eq. (2.1) of the source: for the persymmetric seven-site Jacobi matrix with zero diagonal that the source builds from a prescribed spectrum {0, x, -x, y, -y, z, -z}, the source gives the first-site amplitude as the bracket (y^2 - x^2)(z^2 - x^2)(z^2 - y^2) + y^2 z^2 (z^2 - y^2) cos(xt) + x^2 z^2 (z^2 - x^2) cos(yt) + x^2 y^2 (y^2 - x^2) cos(zt) divided by 2 y^2 (z^2 - x^2)(x^2 - y^2 + z^2). For that matrix P = x^2 z^2 (y^2 - x^2)(z^2 - y^2) / (2 (x^2 - y^2 + z^2)), and the displayed expression is the same function. The formula is known beyond that matrix: for every persymmetric Jacobi matrix with symmetric spectrum, of any order, it is the Proposition \"Amplitude Formulas\" of Escobar, Garcia and Minenkova, arXiv:2606.04353, with the weights of Hochstadt's theorem, and by Kay's criterion every chain with perfect state transfer between its ends is persymmetric. The statement here is the Lean derivation of the seven-site case from the hypothesis of transfer at the time T and the symmetry of the spectrum, through the spectral weights under perfect state transfer, together with the three phases.")),
                "symmetric_spectrum_end_amplitude", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Fusion)),
            Node("reduction", "Integer spectrum, cosine-sum amplitude and earlier transfer times", ReductionFormula(),
                Paragraph(Text("The notation is that of the previous statement; (n : R) is the real number equal to the natural number n, and g | a means that g divides a. Let T > 0 and let x < y < z be the positive eigenvalues of the previous statement. From exp(i T x) = -1 the number T x / pi is an odd integer, and it is positive, so T x / pi = a for an odd natural number a; likewise T y / pi = b is an even natural number and T z / pi = c an odd one, and 0 < a < b < c. Hence the eigenvalues in increasing order are pi/T times -c, -b, -a, 0, a, b, c. Substituting x = pi a / T, y = pi b / T, z = pi c / T in the amplitude of the previous statement and clearing denominators gives kappa N(a, b, c; pi tau / T) with kappa = P (T/pi)^6 / (a^2 b^2 c^2 (b^2 - a^2)(c^2 - a^2)(c^2 - b^2)) > 0, where N(a, b, c; t) = (b^2 - a^2)(c^2 - a^2)(c^2 - b^2) + b^2 c^2 (c^2 - b^2) cos(at) + a^2 c^2 (c^2 - a^2) cos(bt) + a^2 b^2 (b^2 - a^2) cos(ct) is the cosine sum "),
                    Ref("D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator"),
                    Text(". If g divides a, b and c, then g is odd and every eigenvalue is pi/T times a multiple n = g m of g, so exp(i (T/g) pi n / T) = exp(i pi m) = exp(i pi g m) = exp(i T pi n / T); the propagators exp(i (T/g) H) and exp(i T H) have the same spectral phases and are equal, which gives perfect state transfer at the time T/g. That the eigenvalues of a chain with perfect state transfer are spaced by odd multiples of pi/T is Kay's criterion, which the source recalls as its Eq. (1.3) for persymmetric Jacobi matrices, and the source notes that coprime positive eigenvalues make pi the first transfer time; the cosine sum is the bracket of Eq. (2.1) of the source at natural frequencies. The reduction is known as well: Section 3 of arXiv:2606.04353 states that a reduced symmetric spectrum of odd order consists of integers of alternating parity with the smallest one odd and greatest common divisor 1, that a common factor of the positive eigenvalues only rescales time, and that the first transfer time of a reduced spectrum is pi. The statement here is its Lean proof for seven sites: the seven-point form of the spectrum with the parities of a, b, c obtained from the phases of the previous statement, the amplitude as a positive multiple of the cosine sum, and perfect state transfer at the times T/g.")),
                "symmetric_spectrum_reduction", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Fusion))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, DocumentBlock body,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("symspectrum-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(body), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Dvd(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Quot(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));
    private static Formula Minus1(Formula value) => new Formula.Negate(value);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Cast(Formula value, Formula type) =>
        Seq(Open, value, Sp, Colon, Sp, type, Close);

    private static Formula Conj(params Formula[] parts)
    {
        Formula result = parts[^1];
        for (var index = parts.Length - 2; index >= 0; index--)
        {
            result = And(parts[index], result);
        }

        return result;
    }

    private static Formula Vec7(
        Formula a0, Formula a1, Formula a2, Formula a3, Formula a4, Formula a5, Formula a6) =>
        Seq(Bang, OpenBracket, a0, Comma, Sp, a1, Comma, Sp, a2, Comma, Sp, a3, Comma, Sp, a4,
            Comma, Sp, a5, Comma, Sp, a6, CloseBracket);

    private static Formula Hamiltonian() => Call("pathHamiltonian", F.Id("r"), F.Id("q"));
    private static Formula Ev(Formula index) => Call("eigenvalues", Hamiltonian(), index);
    private static Formula Transfer(Formula time) =>
        Call("HasPST", Hamiltonian(), time, D(0), Call("last", D(6)));
    private static Formula Propagator(Formula time) =>
        Call("hamiltonianPropagator", Hamiltonian(), time, D(0), D(0));
    private static Formula Phase(Formula time, Formula value) =>
        Call("exp", Mul(Mul(Cast(time, Complexes()), F.Id("I")), Cast(value, Complexes())));

    private static Formula Chain(Formula body)
    {
        Formula r = F.Id("r"), j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        Formula positive = All("j", FinOf(D(6)), Less(D(0), App(r, j)));
        Formula symmetric = All("k", FinOf(D(7)), Some("l", FinOf(D(7)),
            Equal(Ev(l), Minus1(Ev(k)))));
        return All("r", Arrow(FinOf(D(6)), Reals()), All("q", Arrow(FinOf(D(7)), Reals()),
            Implies(positive, Implies(symmetric, body))));
    }

    private static Formula AmplitudeFormula()
    {
        Formula r = F.Id("r"), time = F.Id("T"), sigma = F.Id("sigma"), x = F.Id("x"), y = F.Id("y"),
            z = F.Id("z"), i = F.Id("i"), tau = F.Id("tau"), t = F.Id("t");
        Formula yx = Sub(Sq(y), Sq(x)), zx = Sub(Sq(z), Sq(x)), zy = Sub(Sq(z), Sq(y));
        Formula bracket = Add(Add(Add(
            Quot(D(1), Mul(Mul(Sq(x), Sq(y)), Sq(z))),
            Quot(Call("cos", Mul(tau, x)), Mul(Mul(Sq(x), yx), zx))),
            Quot(Call("cos", Mul(tau, y)), Mul(Mul(Sq(y), yx), zy))),
            Quot(Call("cos", Mul(tau, z)), Mul(Mul(Sq(z), zx), zy)));
        Formula weightProduct = Parenthesized(Seq(
            new Formula.Subscript(Prod, Seq(t, Sp, InMacro, Sp, FinOf(D(6)))), Sp, App(r, t)));
        Formula amplitude = All("tau", Reals(), Equal(Propagator(tau),
            Cast(Mul(weightProduct, bracket), Complexes())));
        Formula spectrum = All("i", FinOf(D(7)), Equal(Ev(App(sigma, i)),
            App(Vec7(Minus1(z), Minus1(y), Minus1(x), D(0), x, y, z), i)));
        Formula conclusion = Some("sigma", Call("Perm", FinOf(D(7))), Some("x", Reals(),
            Some("y", Reals(), Some("z", Reals(), Conj(Less(D(0), x), Less(x, y), Less(y, z),
                spectrum, Equal(Phase(time, x), Minus1(D(1))), Equal(Phase(time, y), D(1)),
                Equal(Phase(time, z), Minus1(D(1))), amplitude)))));
        return Disp(Chain(All("T", Reals(), Implies(Transfer(time), conclusion))));
    }

    private static Formula ReductionFormula()
    {
        Formula time = F.Id("T"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), sigma = F.Id("sigma"),
            kappa = F.Id("kappa"), i = F.Id("i"), tau = F.Id("tau"), g = F.Id("g");
        Formula ra = Cast(a, Reals()), rb = Cast(b, Reals()), rc = Cast(c, Reals());
        Formula spectrum = All("i", FinOf(D(7)), Equal(Ev(App(sigma, i)),
            Mul(Quot(Pi, time), App(Vec7(Minus1(rc), Minus1(rb), Minus1(ra), D(0), ra, rb, rc), i))));
        Formula amplitude = All("tau", Reals(), Equal(Propagator(tau),
            Cast(Mul(kappa, Call("amplitudeNumerator", a, b, c, Quot(Mul(Pi, tau), time))),
                Complexes())));
        Formula divisors = All("g", Naturals(), Implies(Dvd(g, a), Implies(Dvd(g, b),
            Implies(Dvd(g, c), Transfer(Quot(time, Cast(g, Reals())))))));
        Formula conclusion = Some("a", Naturals(), Some("b", Naturals(), Some("c", Naturals(),
            Some("sigma", Call("Perm", FinOf(D(7))), Some("kappa", Reals(), Conj(
                Call("Odd", a), Call("Even", b), Call("Odd", c), Less(D(0), a), Less(a, b),
                Less(b, c), Less(D(0), kappa), spectrum, amplitude, divisors))))));
        return Disp(Chain(All("T", Reals(),
            Implies(Less(D(0), time), Implies(Transfer(time), conclusion)))));
    }
}
