using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class CliffordThirdMomentNegativityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/zhu2024thirdmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zhu, Mao and Yi define the third-moment expectation kappa of a normalized qudit state against a stochastic Lagrangian subspace. The pointwise bound in their Conjecture 2 fails in prime dimension eleven: a one-qudit state has expectation -1196/64000. This refutes that clause and hence the conjecture as printed; the aggregate clauses are not separately refuted.",
        H("A negative Clifford third-moment expectation"),
        Blocks(
            Node("stochastic", "Stochastic Lagrangian subspaces", StochasticFormula(),
                "For three copies, the quadratic form is x dot x minus y dot y. A stochastic Lagrangian subspace is isotropic for this form, has dimension three, and contains the pair of all-ones vectors.",
                "IsStochasticLagrangian", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("operator", "The tensor-power operator", OperatorFormula(),
                "The source convention is r(T) = sum over (x;y) in T of |x><y|. Regrouping r(T) tensor n into three n-qudit copies gives the matrix R: each column j contributes the indicator that its pair of three-component vectors belongs to T.",
                "R", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("state", "Three copies of a pure-state density matrix", StateFormula(),
                "The matrix of (|Psi><Psi|) tensor three has the displayed product of amplitudes and conjugate amplitudes.",
                "stateCube", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("expectation", "The trace expectation", KappaFormula(),
                "The expectation is the trace of R times stateCube, in the source bra-ket convention. The nonzero dimension hypothesis makes the computational basis finite.",
                "kappa", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The pointwise bound of Conjecture 2", ClaimFormula(),
                "The assertion ranges over every odd prime dimension, every number of qudits, every normalized complex amplitude vector and every stochastic Lagrangian subspace. The complex order requires a zero imaginary part and bounds the real part between zero and one.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A normalized state violates the lower bound", new Formula.Not(F.Id("claim")),
                "Over ZMod 11, let O have diagonal entries 7 and off-diagonal entries 8, and let T be the range of y mapped to (Oy,y). The identities transpose(O) O = I and O 1 = 1 make T stochastic Lagrangian; injectivity gives dimension three. Let v = (-2,0,-2i,1-2i,-1-i,1+2i,-1-2i,-2,-2i,2-i,1-i), whose squared norm is 40, and set Psi(x) = v(x(0))/sqrt(40). The trace reduces to 40^(-3) times the sum, over all y in (ZMod 11)^3, of the product of v(y(k)) conjugate(v((Oy)(k))). This Gaussian-integer sum is exactly -1196, with zero imaginary part. Thus kappa = -1196/64000 < 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-2024-clifford-third-moment-kappa-negativity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("clifford-third-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Of(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Field(Formula d) => Call("ZMod", d);
    private static Formula Config(Formula d, Formula n) => Arrow(Fin(n), Field(d));
    private static Formula Triples(Formula d, Formula n) => Arrow(Fin(D(3)), Config(d, n));
    private static Formula Vectors(Formula d, Formula n) => Arrow(Config(d, n), Complex());
    private static Formula PairType(Formula d) =>
        Seq(Par(Config(d, D(3))), Sp, Times, Sp, Par(Config(d, D(3))));
    private static Formula Subspaces(Formula d) => Call("Submodule", Field(d), PairType(d));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula First(Formula p) => Call("fst", p);
    private static Formula Second(Formula p) => Call("snd", p);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Square(Formula a) => new Formula.Power(a, D(2));
    private static Formula Conj(Formula a) => Call("star", a);
    private static Formula Sum(Formula x, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, Par(body));
    private static Formula Prod(Formula x, Formula type, Formula body) =>
        Seq(F.Prod, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, Par(body));
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Seq(Open, x, Sp, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula StochasticFormula()
    {
        Formula d = F.Id("d"), t = F.Id("T"), p = F.Id("p"), k = F.Id("k");
        Formula xx = Mul(Of(First(p), k), Of(First(p), k));
        Formula yy = Mul(Of(Second(p), k), Of(Second(p), k));
        Formula quadratic = All(p, PairType(d), Imp(Mem(p, t),
            Eq(Sub(Sum(k, Fin(D(3)), xx), Sum(k, Fin(D(3)), yy)), D(0))));
        Formula one = Lambda(k, Fin(D(3)), D(1));
        return All(d, Nat(), All(t, Subspaces(d), Iff(Call("IsStochasticLagrangian", d, t),
            And(quadratic, And(Eq(Call("finrank", Field(d), t), D(3)), Mem(Pair(one, one), t))))));
    }

    private static Formula OperatorFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), t = F.Id("T"), x = F.Id("X"), y = F.Id("Y");
        Formula j = F.Id("j"), k = F.Id("k");
        Formula columns = Pair(Lambda(k, Fin(D(3)), Of(Of(x, k), j)),
            Lambda(k, Fin(D(3)), Of(Of(y, k), j)));
        Formula indicator = Call("ite", Mem(columns, t), D(1), D(0));
        return All(d, Nat(), All(n, Nat(), All(t, Subspaces(d),
            All(x, Triples(d, n), All(y, Triples(d, n),
                Eq(Call("R", d, n, t, x, y), Prod(j, Fin(n), indicator)))))));
    }

    private static Formula StateFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), x = F.Id("X"), y = F.Id("Y");
        Formula k = F.Id("k");
        return All(d, Nat(), All(n, Nat(), All(psi, Vectors(d, n),
            All(x, Triples(d, n), All(y, Triples(d, n),
                Eq(Call("stateCube", psi, x, y),
                    Prod(k, Fin(D(3)), Mul(Of(psi, Of(x, k)), Conj(Of(psi, Of(y, k)))))))))));
    }

    private static Formula KappaFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), t = F.Id("T");
        return All(d, Nat(), All(n, Nat(), Imp(Ne(d, D(0)),
            All(psi, Vectors(d, n), All(t, Subspaces(d), Eq(Call("kappa", d, n, psi, t),
                Call("trace", Mul(Call("R", d, n, t), Call("stateCube", psi)))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), t = F.Id("T"), x = F.Id("x");
        Formula normalized = Eq(Sum(x, Config(d, n), Square(new Formula.Norm(Of(psi, x)))), D(1));
        Formula value = Call("kappa", d, n, psi, t);
        return Iff(F.Id("claim"), All(d, Nat(), Imp(Call("Prime", d), Imp(Ne(d, D(2)),
            All(n, Nat(), All(psi, Vectors(d, n), Imp(normalized,
                All(t, Subspaces(d), Imp(Call("IsStochasticLagrangian", d, t),
                    And(Le(D(0), value), Le(value, D(1))))))))))));
    }
}
