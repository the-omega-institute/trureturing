using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class CliffordThirdMomentAggregateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/zhu2024thirdmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The isotropic aggregate in Zhu, Mao and Yi's Conjecture 2 sums the third-moment expectations over stochastic orthogonal graph subspaces. A normalized two-qudit state in prime dimension five has aggregate 140241723/24017978, strictly below six.",
        H("An isotropic aggregate below six"),
        Blocks(
            Node("graph", "The oriented graph subspace", GraphFormula(),
                "For a three by three matrix O over ZMod d, the graph consists of pairs (Oy,y). The first component is the output and the second component is the input, as in the source operator r(T).",
                "graphSubspace", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("group", "Stochastic orthogonal matrices", GroupFormula(),
                "The stochastic orthogonal group contains every matrix O satisfying transpose(O) O = I and O times the all-ones vector equals the all-ones vector. These matrices index the isotropic graph subspaces; different matrices have different graphs.",
                "stochasticOrthogonal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("aggregate", "The aggregate isotropic expectation", AggregateFormula(),
                "The collection of isotropic subspaces is the set of graphs of stochastic orthogonal matrices. Its aggregate is the sum of kappa over exactly those graphs. The expectation kappa, the tensor operator R and the density tensor stateCube use the source trace convention.",
                "kappaIso", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The aggregate lower bound in Conjecture 2", ClaimFormula(),
                "The assertion quantifies over every prime dimension other than two, every number of qudits and every normalized complex state. The complex order requires that the aggregate have zero imaginary part and real part at least six.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A two-qudit state refutes the bound", new Formula.Not(F.Id("claim")),
                "Take d = 5 and n = 2. The row labels the first qudit and the column labels the second. The integer amplitude matrix has rows (8,-5,0,4,5), (0,3,6,4,-4), (-2,-5,-3,0,3), (-3,0,5,-8,-6), (5,-4,2,-5,0). Divide each amplitude by sqrt(458); the sum of squared amplitudes is 458. The stochastic orthogonal group has twelve matrices: the six permutation matrices and the six row permutations of the matrix with rows (3,4,4), (4,3,4), (4,4,3). For a graph, the trace collapses to a sum over three input copies, with O acting separately on each qudit column. Permuting the rows leaves this expectation unchanged. Each permutation matrix gives one, while each of the other six matrices gives -2577430/(458^3). The latter numerator is the exact integer sum of 15625 products of six amplitudes. Thus the aggregate is 140241723/24017978, and six times the denominator exceeds the numerator by 3866145.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-2024-clifford-third-moment-aggregate-lower-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("clifford-aggregate-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Of(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Field(Formula d) => Call("ZMod", d);
    private static Formula Config(Formula d, Formula n) => Arrow(Fin(n), Field(d));
    private static Formula Vectors(Formula d, Formula n) => Arrow(Config(d, n), Complex());
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Square(Formula a) => new Formula.Power(a, D(2));
    private static Formula Sum(Formula x, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula Mat(Formula d) => Call("Matrix", Fin(D(3)), Fin(D(3)), Field(d));
    private static Formula Instance(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket, Sp);
    private static Formula One(Formula d) => Lambda(F.Id("k"), Fin(D(3)), D(1));
    private static Formula Transpose(Formula o) => Call("transpose", o);

    private static Formula GraphFormula()
    {
        Formula d = F.Id("d"), o = F.Id("O"), y = F.Id("y");
        return All(d, Nat(), All(o, Mat(d),
            Eq(Call("graphSubspace", o), Call("range", Lambda(y, Config(d, D(3)),
                Pair(Call("mulVec", o, y), y))))));
    }

    private static Formula GroupFormula()
    {
        Formula d = F.Id("d"), o = F.Id("O");
        Formula condition = And(Eq(Mul(Transpose(o), o), D(1)),
            Eq(Call("mulVec", o, One(d)), One(d)));
        return All(d, Nat(), Seq(Instance("NeZero", d),
            Eq(Call("stochasticOrthogonal", d),
                Call("filter", Lambda(o, Mat(d), condition), Call("univ", Mat(d))))));
    }

    private static Formula AggregateFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), o = F.Id("O");
        Formula domain = Seq(o, Sp, Colon, Sp, Mat(d), Comma, Sp,
            o, Sp, InMacro, Sp, Call("stochasticOrthogonal", d));
        Formula sum = Seq(F.Sum, Underscore, Grp(domain), Sp,
            Parenthesized(Call("kappa", d, n, psi, Call("graphSubspace", o))));
        return All(d, Nat(), All(n, Nat(), Seq(Instance("NeZero", d),
            All(psi, Vectors(d, n), Eq(Call("kappaIso", d, n, psi), sum)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), x = F.Id("x");
        Formula normalized = Eq(Sum(x, Config(d, n), Square(new Formula.Norm(Of(psi, x)))), D(1));
        return Iff(F.Id("claim"), All(d, Nat(), Seq(
            Instance("Fact", Call("Prime", d)), Imp(Ne(d, D(2)),
                All(n, Nat(), All(psi, Vectors(d, n), Imp(normalized,
                    Le(D(6), Call("kappaIso", d, n, psi)))))))));
    }
}
