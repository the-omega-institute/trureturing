using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.BlockNorm;

internal sealed class SpikeEdgeEstimateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.";
    private static readonly Formula I = Iota, X = F.Id("X"), S = F.Id("S"), V = F.Id("v"), Z = F.Id("z"), T = F.Id("t"), L = F.Id("L");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one diagonal spike in a Hermitian block matrix admits two-sided spectral-edge estimates. For a unit v, Hermitian S with Sv = 0, L >= 1 and L >= ‖K X S‖, every t >= 96L has an error at most 891L^4/t^3 at each edge, and 1782L^4/t^3 in their sum.",
        H("Quantitative edges of a positive and negative block spike"),
        Blocks(
            Node("edgeMax", "Top spectral edge", EdgeDefinition(true), "The real supremum of the real spectrum. Hermitian matrices on nonempty finite types have a nonempty compact real spectrum.", DescribeRole.Definition),
            Node("edgeMin", "Bottom spectral edge", EdgeDefinition(false), "The real infimum of the real spectrum, using the same real-spectrum convention as the top edge.", DescribeRole.Definition),
            Node("K", "Hermitian block pencil", Pencil(), "K X D is Matrix.fromBlocks D X (Matrix.conjTranspose X) (-D); it is Hermitian when D is Hermitian.", DescribeRole.Definition),
            Node("upper_shift_iff", "Upper spectral shift", UpperShift(), "A scalar upper spectral bound is exactly positivity of the scalar shift minus the Hermitian matrix.", DescribeRole.Lemma),
            Node("outer_action", "Action of a rank-one matrix", OuterAction(), "Matrix.vecMulVec and WithLp.ofLp are the actual matrix and vector carriers. The scalar is the complex inner product.", DescribeRole.Lemma),
            Node("outer_hermitian", "Hermitian rank-one matrix", Over(All(V, Vec(I), Hermitian(Outer(V))), false), "The conjugate transpose of the rank-one matrix equals the matrix itself.", DescribeRole.Lemma),
            Node("defect1", "First edge-sum coefficient", Over(All(X, Mat(I), All(V, Vec(I), Eq(Call("defect1", X, V), Defect1()))), false), "The first coefficient measures the squared norm difference between the adjoint action and the original action.", DescribeRole.Definition),
            Node("defect2", "Second edge-sum coefficient", Over(All(X, Mat(I), All(S, Mat(I), All(V, Vec(I), Eq(Call("defect2", X, S, V), Defect2())))), false), "The second coefficient is the difference of the real S-pairings, with the original action first and the adjoint action second.", DescribeRole.Definition),
            Node("positive_spike_enclosure", "Two-sided positive-edge enclosure", Enclosure(false), "The normalized test vector is formed from e + εr₁ + ε²r₂ at ε = 1/t. Its Rayleigh quotient supplies the lower edge bound; the complement gap and residual-energy estimate supply the upper bound. Both estimates hold at every finite t >= 96L.", DescribeRole.Theorem),
            Node("edge_sum_bound", "Two-sided edge-sum enclosure", Enclosure(true), "Unitary block reflection transfers the positive-edge estimate to the negative edge. Their leading ±t terms cancel. The sum has the corrected coefficient ‖X* v‖² - ‖X v‖² at order 1/t and the difference of the S-pairings at order 1/t².", DescribeRole.Theorem)), []));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bl-spike-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Over(Formula body, bool nonempty) => All(I, F.Id("Type"), Inst(Call("Fintype", I), Inst(Call("DecidableEq", I), nonempty ? Inst(Call("Nonempty", I), body) : body)));
    private static Formula Pencil()
    {
        Formula d = F.Id("D");
        return Over(All(X, Mat(I), All(d, Mat(I), Eq(Call("K", X, d), QCall("Matrix", "fromBlocks", d, X, Adj(X), Minus(d))))), false);
    }
    private static Formula EdgeDefinition(bool maximum)
    {
        Formula m = F.Id("M");
        return Over(All(m, Mat(I), Eq(Call(maximum ? "edgeMax" : "edgeMin", m), Call(maximum ? "sSup" : "sInf", Call("spectrum", Real(), m)))), false);
    }
    private static Formula UpperShift()
    {
        Formula m = F.Id("M"), c = F.Id("c"), x = F.Id("x");
        Formula bound = All(x, Real(), Imp(Member(x, Call("spectrum", Real(), m)), Le(x, c)));
        return Over(All(m, Mat(I), Imp(Hermitian(m), All(c, Real(), IffOf(Positive(Sub(Smul(c, D(1)), m)), bound)))), false);
    }
    private static Formula OuterAction() => Over(All(V, Vec(I), All(Z, Vec(I), Eq(Act(Outer(V), Z), Smul(Inner(V, Z), V)))), false);
    private static Formula Defect1() => Sub(Pow(Norm(Act(Adj(X), V)), D(2)), Pow(Norm(Act(X, V)), D(2)));
    private static Formula Pair(bool adjoint) => RePart(Inner(Act(adjoint ? Adj(X) : X, V), Act(S, Act(adjoint ? Adj(X) : X, V))));
    private static Formula Defect2() => Sub(Pair(false), Pair(true));
    private static Formula Enclosure(bool sum)
    {
        Formula k = Call("K", X, Add(Smul(T, Outer(V)), S));
        Formula error;
        if (sum) error = Abs(Sub(Add(Call("edgeMax", k), Call("edgeMin", k)), Parenthesized(Add(Div(Call("defect1", X, V), T), Div(Call("defect2", X, S, V), Pow(T, D(2)))))));
        else
        {
            Formula a = Sub(Pow(Norm(Act(Adj(X), V)), D(2)), Div(Pow(Norm(Inner(V, Act(X, V))), D(2)), D(2)));
            Formula expansion = Sub(Add(T, Div(a, T)), Div(Pair(true), Pow(T, D(2))));
            error = Abs(Sub(Call("edgeMax", k), Parenthesized(expansion)));
        }
        Formula rhs = Div(Mul(sum ? D(1, 7, 8, 2) : D(8, 9, 1), Pow(L, D(4))), Pow(T, D(3)));
        Formula rest = Imp(Eq(Norm(V), D(1)), Imp(Hermitian(S), Imp(Eq(Act(S, V), D(0)), Imp(Le(D(1), L), Imp(Le(Norm(Call("K", X, S)), L), Imp(Le(Mul(D(9, 6), L), T), Le(error, rhs)))))));
        return Over(All(X, Mat(I), All(S, Mat(I), All(V, Vec(I), All(T, Real(), All(L, Real(), rest))))), true);
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Minus(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(Formula i) => Call("Matrix", i, i, Complex());
    private static Formula Vec(Formula i) => Call("EuclideanSpace", Complex(), i);
    private static Formula Star(Formula a) => Call("star", a);
    private static Formula Adj(Formula a) => QCall("Matrix", "conjTranspose", a);
    private static Formula Inner(Formula a, Formula b) => new Formula.Subscript(Seq(Langle, Sp, a, Comma, Sp, b, Sp, Rangle), Complex());
    private static Formula RePart(Formula a) => QCall("Complex", "re", a);
    private static Formula Act(Formula a, Formula v) => App(QCall("Matrix", "toEuclideanCLM", a), v);
    private static Formula Outer(Formula v) => QCall("Matrix", "vecMulVec", QCall("WithLp", "ofLp", v), Star(QCall("WithLp", "ofLp", v)));
    private static Formula Hermitian(Formula a) => QCall("Matrix", "IsHermitian", a);
    private static Formula Positive(Formula a) => QCall("Matrix", "PosSemidef", a);
}
