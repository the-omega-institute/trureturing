using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class HyperbolicScalarZetaIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/nishioka2021freescalar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural number k, the combination of harmonic numbers, Bernoulli numbers and values of the Riemann zeta function at the non-positive integers displayed as eq. (C.12) of T. Nishioka and Y. Sato (arXiv:2101.02399, JHEP 05 (2021) 074) vanishes. The authors checked it numerically up to k = 100 and wrote that they do not know a proof; they use it to simplify the derivative of the spectral zeta function of a conformally coupled free scalar on even-dimensional hyperbolic space. That use is not formalized here: the statement below is the identity itself.",
        H("A Bernoulli-harmonic-zeta identity for the free scalar on hyperbolic space"),
        Blocks(
            Node("claim", "The identity", ClaimFormula(),
                "Eq. (C.12) of the paper, for every k. The sum over m runs over 1 <= m <= k (empty for k = 0) and the sum over j over range(2k + 2) = {0, ..., 2k + 1}. H_n is the harmonic number harmonic(n) = 1 + 1/2 + ... + 1/n (with H_0 = 0), B_n the Bernoulli number bernoulli(n) with B_1 = -1/2, and riemannZeta the Riemann zeta function, evaluated at -j; the rational numbers are read in the complex numbers. The exponents -(2k + 2), 2k - j and -(2k + 1) of 2 are integers, so 2^(2k - j) is 1/2^(j - 2k) for j > 2k.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the identity", Disp(F.Id("claim")),
                "Replace riemannZeta(-j) by (-1)^j B_(j+1)/(j+1) and multiply by 2^(2k+2)(k+1); put N = 2k + 2 and b_m = sum over i of C(m, i) 2^i B_i. Since b_m = 2^m B_m(1/2), the value B_m(1/2) = (2^(1-m) - 1) B_m of the Bernoulli polynomial at 1/2 gives b_m = (2 - 2^m) B_m; in particular b_m = 0 for odd m. The middle sum becomes the sum of b_i (1/i + 1/(N - i)) over 1 <= i <= N - 1, and the zeta sum becomes the sum of C(N, i) 2^i B_i H_(i-1) over 1 <= i <= N. Two harmonic-binomial identities, C(n, i)(H_n - H_i) = sum over j = 1..n of C(n - j, i)/j (by Pascal's rule and induction) and the transform of C(n, i) 2^i B_i / i into the sum of (b_j - 1)/j (by induction on n), rewrite the zeta sum through sums of b_i/i and b_(N-i)/i. These cancel against the middle sum, and what is left is -H_(N-1) - 1/N + H_N = 0 after b_N = (2 - 2^N) B_N is used.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nishioka-sato-2021-bernoulli-harmonic-zeta-identity"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("nishioka-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(F.Id(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TwoK(byte offset) => Add(Mul(D(2), F.Id("k")), D(offset));

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), j = F.Id("j");
        Formula two = D(2);
        Formula first = Mul(
            new Formula.Negate(Parenthesized(Div(Pow(two, new Formula.Negate(Parenthesized(TwoK(2)))),
                Add(k, D(1))))),
            Call("harmonic", TwoK(1)));
        Formula middle = SumOver(Member(m, Call("Icc", D(1), k)), Mul(
            Div(Mul(Pow(two, new Formula.Negate(Parenthesized(TwoK(2)))),
                    Parenthesized(Sub(Pow(two, Mul(two, m)), two))),
                Add(Sub(k, m), D(1))),
            Parenthesized(Div(Call("bernoulli", Mul(two, m)), Mul(two, m)))));
        Formula zeta = SumOver(Member(j, Call("range", TwoK(2))), Mul(Mul(Mul(
            Div(Pow(Parenthesized(new Formula.Negate(D(1))), j), Pow(two, Sub(Mul(two, k), j))),
            Call("choose", TwoK(1), j)),
            Call("harmonic", j)),
            Call("riemannZeta", new Formula.Negate(j))));
        Formula last = Mul(Mul(
            Parenthesized(Sub(D(1), Pow(two, new Formula.Negate(Parenthesized(TwoK(1)))))),
            Call("harmonic", TwoK(1))),
            Parenthesized(Div(Call("bernoulli", TwoK(2)), Add(k, D(1)))));
        Formula total = Add(Add(Sub(first, Parenthesized(middle)), Parenthesized(zeta)), last);
        return Disp(Iff(F.Id("claim"), All("k", Nats(), Equal(total, D(0)))));
    }
}
