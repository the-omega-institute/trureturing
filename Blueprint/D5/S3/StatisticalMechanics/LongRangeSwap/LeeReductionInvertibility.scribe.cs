using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.LongRangeSwap;

internal sealed class LeeReductionInvertibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/lee2026longrangeswap");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every reduction operator is a unit for all species counts, word lengths, valid block positions, and parameters in the closed unit cube.",
        H("Lee's reduction operators are invertible"),
        Blocks(
            Node("a", "Lee's reduction recursion", "A", AFormula(), "Equation (28), source label 1122am331, defines A zero as the identity and the next A by the displayed matrix-inverse recursion. The carrier is Matrix (Fin n to Fin N) (Fin n to Fin N) over the reals; 1 denotes its identity matrix. Implicit sizes N and n are shown explicitly.", literature: true),
            Node("claim", "Lee's invertibility conjecture", "claim", ClaimFormula(), "Remark 3.1, page 18: These results lead us to conjecture that 𝔄_k is invertible for all parameters μ_i ∈ [0,1]. The encoding quantifies over every N at least one, n at least two, one-indexed block start j at least one, and k with j + k + 1 at most n. Species are Fin N; words are Fin n to Fin N; invertibility means IsUnit of the full word-coordinate matrix. The parameters include the endpoints zero and one.", literature: true),
            Node("result", "Proof of invertibility on the entire parameter cube", "result", Disp(F.Id("claim")), "Positive-weight collision paths reach the absorbing boundary in at most 2 N m steps. The two outgoing masses sum to one on each interior row. The attained-maximum principle forces every zero-boundary harmonic block chain to vanish. Extending a vector backwards through the already invertible pivots and using uniqueness proves the next pivot has zero kernel, hence is a unit. Induction identifies these pivots with the literal reduction recursion. The stochastic walk includes absorbing boundary rows; its restriction to interior rows is substochastic.", DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-2026-reduction-operator-invertibility"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role = DescribeRole.Definition, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("lee-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula NatBind(Formula body, params string[] names)
    {
        for (int i = names.Length - 1; i >= 0; i--) body = All(names[i], Nat(), body);
        return body;
    }

    private static Formula AFormula()
    {
        Formula N = F.Id("N"), n = F.Id("n"), mu = F.Id("mu"), j = F.Id("j"), k = F.Id("k");
        Formula cb = QCall("LeeCollisionExit", "calB", N, n, mu, j, Add(k, D(2)));
        Formula cbp = App(Qualified("LeeCollisionExit", "calBprime"), N, n, mu, j, Add(k, D(1)));
        Formula inverse = new Formula.Power(Parenthesized(Call("A", N, n, mu, j, k)), new Formula.Negate(D(1)));
        Formula recurrence = Eq(Call("A", N, n, mu, j, Add(k, D(1))), Sub(D(1), Mul(Mul(cb, inverse), cbp)));
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), All("j", Nat(),
            And(Eq(Call("A", N, n, mu, j, D(0)), D(1)), All("k", Nat(), recurrence)))), "N", "n"));
    }
    private static Formula ClaimFormula()
    {
        Formula N = F.Id("N"), n = F.Id("n"), j = F.Id("j"), k = F.Id("k"), mu = F.Id("mu"), a = F.Id("a");
        Formula range = All("a", Fin(N), And(Le(D(0), App(mu, a)), Le(App(mu, a), D(1))));
        Formula claim = NatBind(Imp(Le(D(1), N), Imp(Le(D(2), n), Imp(Le(D(1), j),
            Imp(Le(Add(Add(j, k), D(1)), n), All("mu", Arr(Fin(N), Real()),
            Imp(range, Call("IsUnit", Call("A", N, n, mu, j, k)))))))), "N", "n", "j", "k");
        return Disp(Eq(F.Id("claim"), claim));
    }

}
