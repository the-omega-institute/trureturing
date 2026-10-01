using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PhotonAddedMajorizationCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024majorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every k at least 2, the coefficients c_n^(kk) that compare k-photon addition with single-photon addition on a two-mode squeezed vacuum are non-negative. This proves the conjecture of Z. Van Herstraeten, N. J. Cerf, S. Guha and C. N. Gagatsos (arXiv:2312.02066), who proved the cases k = 2, ..., 8.",
        H("Non-negativity of the photon-addition coefficients"),
        Blocks(
            Node("expansion", "The expansion defining the coefficients", ExpansionFormula(),
                "For natural numbers k and a sequence c of real numbers indexed by n >= 0, Expansion(k, c) is the expansion of the paper, C(n+k+1, k)^2 = sum over i from 0 to n+1 of c_(n-i)^(kk) (i+1)^2 for every n >= 0, with c_n^(kk) = c(n) for n >= 0 and c_(-1)^(kk) = 1, so that the term i = n+1 is (n+2)^2. Here C(a, b) is the binomial coefficient.",
                "Expansion", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The photon-addition conjecture", ClaimFormula(),
                "For every natural number k >= 2, a sequence c with Expansion(k, c) exists, and every such sequence takes only non-negative values. The expansion determines c(n) from c(0), ..., c(n-1), so these are the coefficients c_n^(kk) of the paper, and their non-negativity is the column stochasticity of the paper's matrix D.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Let N_k(x) be the power series with coefficients C(n+k, k)^2. The expansion says (1 + sum of c(n) x^(n+1)) N_1 = N_k. First, N_1 = (1+x)(1-x)^(-3), since C(n+2, 2) + C(n+1, 2) = (n+1)^2. Second, by Vandermonde's identity C(n+k, k) is the sum over j of C(k, j) C(n, j), and C(n+k, k) C(n, j) = C(k+j, j) C(n+k, k+j); so with a_j = C(k, j) C(k+j, j), N_k is the sum over j from 0 to k of a_j x^j (1-x)^(-(k+j+1)). Let E = (1-x^2)^(-1), the series 1 + x^2 + x^4 + ..., and let B = (1 + (k^2+k-1) x)(1-x)^(-(k-2)) E + sum over j from 2 to k of a_j x^j (1-x)^(-(k+j-3)) E. Since E(1+x) = (1-x)^(-1), (1 - x)(1-x)^(-(k+2)) = (1-x)^(-(k+1)), a_0 = 1 and a_1 = k(k+1), one gets B N_1 = N_k. For k >= 2 every factor of B has non-negative coefficients and B has constant term 1, so c(n) = [x^(n+1)] B is a solution. As N_1 is not a zero divisor, every solution equals it, and its values are non-negative.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("van-herstraeten-2024-photon-addition-coefficients"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("photon-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula SomeIn(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Sequences() =>
        Seq(Mathbb, Grp(F.Id("R")), Caret, Grp(Mathbb, Grp(F.Id("N"))));
    private static Formula At(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula ExpansionOf(Formula k, Formula c) => Call(F.Id("Expansion"), k, c);

    private static Formula ExpansionFormula()
    {
        Formula k = F.Id("k"), c = F.Id("c"), n = F.Id("n"), i = F.Id("i");
        Formula lhs = Square(Call(F.Id("C"), Add(Add(n, k), D(1)), k));
        Formula sum = Seq(F.Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n), Sp,
            Mul(At(c, Sub(n, i)), Square(Parenthesized(Add(i, D(1))))));
        Formula rhs = Add(sum, Square(Parenthesized(Add(n, D(2)))));
        return Disp(Iff(ExpansionOf(k, c), AllIn(n, Naturals(), Equal(lhs, rhs))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), c = F.Id("c"), n = F.Id("n");
        Formula existence = SomeIn(c, Sequences(), ExpansionOf(k, c));
        Formula positivity = AllIn(c, Sequences(),
            Implies(ExpansionOf(k, c),
                AllIn(n, Naturals(), Rel(D(0), FormulaRelationOperator.LessThanOrEqual, At(c, n)))));
        Formula body = AllIn(k, Naturals(),
            Implies(Rel(k, FormulaRelationOperator.GreaterThanOrEqual, D(2)), And(existence, positivity)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
