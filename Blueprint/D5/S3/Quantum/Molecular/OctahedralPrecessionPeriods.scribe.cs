using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Molecular;

internal sealed class OctahedralPrecessionPeriodsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/klee2018a318245");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients a(n) of OEIS A318245, the scaled period of the precession of the angular momentum vector J along a curve of the rotational energy surface of an octahedral molecule, are integers divisible by 3 for every n at least 1, as conjectured by Bradley Klee in 2018. The proof gives the closed form a(n) = sum over k + j = n of C(2k,k) C(2j,j) C(2k+j,k) 4^j and shows that it is multiplicative in the base-3 digits of n modulo 3.",
        H("Octahedral precession periods modulo 3"),
        Blocks(
            Node("sequence", "The sequence A318245", SequenceFormula(),
                "The scaled generating function T(v) = sum of a(n) (3v/64)^n satisfies 9(5v - 4)T + d/dv(16v(v - 1)(3v - 4)T') = 0 with a(0) = 1. Comparing the coefficients of v^n gives a(1) = 12 from the constant term and the three-term recurrence of the entry for every n at least 2; the sequence is defined over the rationals, where the recurrence divides by 3n^2.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Klee's conjecture", ClaimFormula(),
                "For every n at least 1, a(n) is three times an integer: a(n) is an integer and a(n) mod 3 = 0.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Let t(k, j) = C(2k,k) C(2j,j) C(2k+j,k) 4^j and b(n) = sum of t(k, j) over k + j = n. Two ratio identities hold in the natural numbers: t(k, j+1)(j+1)(k+j+1) = 8 t(k, j)(2j+1)(2k+j+1) and 4 t(k+1, j)(k+1)^2(2j+1) = t(k, j+1)(2k+1)(j+1)(2k+j+2). Put n = N + 2 and G(k) = t(k, n-k) R(k) with R(k) = 2k^2 n(4kn - 4n^2 + 6n - 3)/((n+k)(n+k-1)(2n-2k-1)). By the ratio identities, 3n^2 t(k, j+2) - 4(28n^2 - 28n + 9) t(k, j+1) + 64(4n-5)(4n-3) t(k, j) = G(k+1) - G(k) for k + j = N, and the two boundary terms k = N+1, N+2 cancel against G(N+1); since G(0) = 0 the sum telescopes, so b satisfies the recurrence of the entry. As b(0) = 1 and b(1) = 12, induction gives a(n) = b(n). By Lucas' theorem at the prime 3, C(2k,k) with k = 3i + s is congruent to C(2s,s) C(2i,i), and C(2k+j,k) splits in the same way with a carry that only occurs when a factor C(2s,s) C(2e,e) C(2s+e,s) with 2s + e at least 3 already vanishes modulo 3; as 4 is congruent to 1, t(3i+s, 3a+e) is congruent to t(s, e) t(i, a) for s, e less than 3. Splitting each k in the sum for b(3m + r) into its last base-3 digit, the terms whose last digits carry vanish and the rest regroup to b(3m + r) congruent to b(r) b(m) modulo 3. Since b(1) = 12 and b(2) = 180 are divisible by 3 and b(0) = 1, strong induction on n gives that 3 divides b(n) for every n at least 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a318245-klee-octahedral-mod3"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("a318245-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula m = Add(n, D(2));
        Formula numerator = Subtract(
            Times(Times(D(4), Parenthesized(Add(Subtract(Times(D(2, 8), Pow(m, D(2))),
                Times(D(2, 8), m)), D(9)))), Call("a", Add(n, D(1)))),
            Times(Times(Times(D(6, 4), Parenthesized(Subtract(Times(D(4), m), D(5)))),
                Parenthesized(Subtract(Times(D(4), m), D(3)))), Call("a", n)));
        Formula step = Equal(Call("a", m),
            new Formula.Fraction(numerator, Times(D(3), Pow(m, D(2)))));
        Formula start = And(Equal(Call("a", D(0)), D(1)), Equal(Call("a", D(1)), D(1, 2)));
        return Disp(And(start, All("n", Naturals(), step)));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), z = F.Id("z");
        Formula body = Implies(Less(D(0), n),
            Some("z", Integers(), Equal(Call("a", n), Times(D(3), z))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All("n", Naturals(), body))));
    }
}
