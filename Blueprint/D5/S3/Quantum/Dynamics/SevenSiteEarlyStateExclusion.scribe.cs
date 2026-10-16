using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class SevenSiteEarlyStateExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/escobar2025earlystateexclusion");

    private static readonly LibraryNoteRef Fusion =
        LibraryNoteRef.Create("D5/L/GraphInvariants/escobar2026spectralfusion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Escobar, Garcia and Minenkova (arXiv:2507.18767, Section 4) conjecture that a 7 x 7 Jacobi matrix with symmetric spectrum realizing perfect state transfer does not have early state exclusion if and only if its positive eigenvalues are integer multiples of the smallest positive eigenvalue, and they prove two one-parameter families of spectra. The conjecture is true: for every chain of seven sites with positive couplings, real potentials and a spectrum closed under negation, and every time T > 0 at which the chain has perfect state transfer between its end sites and before which it has none, the first-site amplitude has no zero in the open interval (0, T) if and only if every positive eigenvalue is an integer multiple of the smallest positive eigenvalue.",
        H("Early state exclusion in seven-site transfer chains with symmetric spectrum"),
        Blocks(
            Node("claim", "The seven-site early state exclusion conjecture", ClaimFormula(),
                Paragraph(Text("Section 4 of the source states: \"Let J be a 7 x 7 Jacobi matrix with symmetric spectrum realizing PST. Then J does not have ESE if and only if its positive eigenvalues are integer multiples of the smallest positive eigenvalue.\" In the source a Jacobi matrix is the real symmetric tridiagonal matrix of its Eq. (1.1), with real diagonal entries and positive off-diagonal entries; it realizes perfect state transfer between the end vertices at the time T > 0 if exp(-iJT) e_0 = exp(i phi) e_N for some real phase phi; its spectrum is symmetric if lambda_j = -lambda_(N - j) for its ordered eigenvalues, which is read here as closure of the spectrum under negation, the definition of arXiv:2606.04353; and it exhibits early state exclusion at the time tau if it realizes perfect state transfer at the earliest time T > 0 and the inner product of exp(-iJ tau) e_0 with e_0 vanishes for some tau in (0, T). Here J is pathHamiltonian(r, q), the Hamiltonian of the path on the seven sites 0, ..., 6 with the couplings r on its six edges, all positive, and the real potentials q on its sites, and eigenvalues(J, k) is the k-th eigenvalue of the Hermitian matrix J in Mathlib's enumeration. Perfect state transfer at the time t is HasPST(J, t, 0, last(6)), which says that the entry of exp(itJ) between the sites 0 and 6 has modulus one; this is the source's condition, because J is real and symmetric, so that the entries of exp(itJ) and exp(-itJ) between the end sites are complex conjugates, and a column of a unitary matrix with an entry of modulus one is that entry times a basis vector. The earliest time is expressed by the three hypotheses 0 < T, transfer at the time T, and no transfer at any time t with 0 < t < T; the statement is quantified over every such T. The amplitude is hamiltonianPropagator(J, tau, 0, 0), the entry of exp(-i tau J) at the first site. The right-hand side says that some positive eigenvalue is the smallest positive eigenvalue and that every positive eigenvalue is an integer multiple of it; (n : R) is the real number equal to the integer n.")),
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", Disp(F.Id("claim")),
                Paragraph(Text("Let T be the earliest transfer time of the chain. By the spectral reduction "),
                    Ref("D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_reduction"),
                    Text(" there are natural numbers 0 < a < b < c, with a and c odd and b even, such that the eigenvalues are pi/T times -c, -b, -a, 0, a, b, c, the first-site amplitude at the time tau is kappa N(a, b, c; pi tau / T) with kappa > 0 and N(a, b, c; t) = (b^2 - a^2)(c^2 - a^2)(c^2 - b^2) + b^2 c^2 (c^2 - b^2) cos(at) + a^2 c^2 (c^2 - a^2) cos(bt) + a^2 b^2 (b^2 - a^2) cos(ct), and the chain has perfect state transfer at the time T/g for every common divisor g of a, b, c. If g = gcd(a, b, c) were larger than 1, then T/g would be a transfer time in (0, T), against the minimality of T; hence gcd(a, b, c) = 1. Since kappa is not zero, the amplitude vanishes at a time tau in (0, T) exactly when N(a, b, c; .) vanishes at t = pi tau / T in (0, pi), and every t in (0, pi) arises from tau = T t / pi in (0, T). By the zero criterion of the cosine sum "),
                    Ref("D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff"),
                    Text(" such a zero exists if and only if a is not 1. The positive eigenvalues are pi a / T < pi b / T < pi c / T, so the smallest positive eigenvalue is pi a / T, and the other two are integer multiples of it exactly when a divides b and c, that is, because gcd(a, b, c) = 1, exactly when a = 1. Hence the amplitude has no zero in (0, T) if and only if every positive eigenvalue is an integer multiple of the smallest one. The source proves two families: its Theorem 3.2 shows that a seven-site Jacobi matrix realizing perfect state transfer with the spectrum {0, 1, -1, 2m, -2m, 2m + 1, -(2m + 1)} does not have early state exclusion, and its Theorem 3.4 shows that the one with the spectrum {0, 2m + 1, -(2m + 1), 2m + 2, -(2m + 2), 2m + 3, -(2m + 3)} has early state exclusion 2m times; it states the general statement as the conjecture of its Section 4 and adds: \"We believe that the techniques used to prove Theorems 3.2 and 3.4 cannot be replicated here.\" The first-site amplitude formula is Eq. (2.1) of the source and the spacing of the spectrum of a chain with perfect state transfer is Kay's criterion, recalled by the source as its Eq. (1.3); the later paper arXiv:2606.04353 of the same authors gives the amplitude formula and the reduction to integer spectra for every order and shows that the analogous characterisation is not true in general for larger chains, without deciding the seven-site statement. Proved here is the equivalence for every seven-site chain with positive couplings, real potentials and symmetric spectrum at its earliest transfer time; the number of zeros of the amplitude is not addressed.")),
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Fusion),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("escobar-garcia-2025-seven-site-early-state-exclusion"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, DocumentBlock body,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("sevensite-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(body), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Minus1(Formula value) => new Formula.Negate(value);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
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

    private static Formula Hamiltonian() => Call("pathHamiltonian", F.Id("r"), F.Id("q"));
    private static Formula Ev(Formula index) => Call("eigenvalues", Hamiltonian(), index);
    private static Formula Transfer(Formula time) =>
        Call("HasPST", Hamiltonian(), time, D(0), Call("last", D(6)));

    private static Formula ClaimFormula()
    {
        Formula r = F.Id("r"), time = F.Id("T"), j = F.Id("j"), k = F.Id("k"), l = F.Id("l"),
            t = F.Id("t"), tau = F.Id("tau"), k0 = F.Id("k0"), n = F.Id("n");
        Formula positive = All("j", FinOf(D(6)), Less(D(0), App(r, j)));
        Formula symmetric = All("k", FinOf(D(7)), Some("l", FinOf(D(7)),
            Equal(Ev(l), Minus1(Ev(k)))));
        Formula earliest = All("t", Reals(), Implies(Less(D(0), t), Implies(Less(t, time),
            new Formula.Not(Transfer(t)))));
        Formula exclusion = Some("tau", Reals(), Conj(Less(D(0), tau), Less(tau, time),
            Equal(Call("hamiltonianPropagator", Hamiltonian(), tau, D(0), D(0)), D(0))));
        Formula smallest = All("k", FinOf(D(7)),
            Implies(Less(D(0), Ev(k)), LessEq(Ev(k0), Ev(k))));
        Formula multiples = All("k", FinOf(D(7)), Implies(Less(D(0), Ev(k)),
            Some("n", Integers(), Equal(Ev(k), Mul(Cast(n, Reals()), Ev(k0))))));
        Formula divisibility = Some("k0", FinOf(D(7)),
            Conj(Less(D(0), Ev(k0)), smallest, multiples));
        Formula body = All("r", Arrow(FinOf(D(6)), Reals()), All("q", Arrow(FinOf(D(7)), Reals()),
            All("T", Reals(), Implies(positive, Implies(symmetric, Implies(Less(D(0), time),
                Implies(Transfer(time), Implies(earliest,
                    Iff(new Formula.Not(exclusion), divisibility)))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
