using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class CZXParentLindbladianOrderedTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.";
    private const string Quantum = "D5.S3.Quantum.";
    private const string TensorNetworks = Quantum + "TensorNetworks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/liuetal2026parentlindbladians");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-time CZX evolution and its fixed-time trace-distance estimate.",
        H("Finite-time CZX evolution and ordered transfer"),
        Blocks(
            Node("blocks", "Cyclic middle pairs", BlocksStatement(),
                "At index k the block records sites 2k+1 and 2k+2 modulo the ring length. The last block ends at site zero."),
            Node("initial", "Initial operator", InitialStatement(),
                "The identity plus the global spin flip has normalization 4 to the power minus m."),
            Node("stationary", "Stationary operator", StationaryStatement(),
                "The same normalization multiplies the identity and the CZX symmetry operator weighted by 2 to the power 1−m."),
            Node("delta", "Canonical trace distance", DeltaStatement(),
                "The readout is half the trace norm of the difference of the actual evolved operator and the stationary operator."),
            Node("evolved_initial_transfer", "Exact ordered transfer", EvolutionStatement(),
                "The original exponential factors over all even starts. On the weighted gauge sector the factors independently refresh the cyclic middle pairs. Summing the second bit of each pair gives the literal transfer letter. Contraction around the cycle traces the product in increasing block order. Both starts on a four-site ring occur in the factorization.",
                DescribeRole.Theorem),
            Node("fixed_time_delta_upper", "Fixed-time quantum bound", BoundStatement(),
                "The evolved difference has the same conjugate-transpose product as the diagonal matrix of absolute coefficients. This diagonal is positive semidefinite, so the trace norm is the sum of those coefficients. Centering the resulting word traces subtracts two. Each diagonal entry is bounded by the Euclidean norm of its corresponding row. Applying annealed growth to both coordinate rows yields the displayed bound. For positive time the growth factor divided by two is strictly below one.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("czx-ordered-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula BlocksStatement()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var x = F.Id("x");
        var left = At(Qualified(Prefix.Replace('/', '.') + "blocks"), m, x, k);
        var odd = Add(Mul(D(2), Call("Fin.val", k)), D(1));
        var even = Add(Mul(D(2), Call("Fin.val", k)), D(2));
        var right = Call("Prod.mk", At(x, Call("Fin.ofNat", RingSize(m), odd)),
            At(x, Call("Fin.ofNat", RingSize(m), even)));
        return All("m", Naturals(), All("x", Config(m), All("k", Call("Fin", m), Eqn(left, right))));
    }

    private static Formula InitialStatement()
    {
        var m = F.Id("m");
        return All("m", Naturals(), Eqn(Local("initial", m), Smul(Inv(Pow(D(4), m)),
            Add(D(1), Window("tensorX", RingSize(m))))));
    }

    private static Formula StationaryStatement()
    {
        var m = F.Id("m");
        return All("m", Naturals(), Eqn(Local("stationary", m), Smul(Inv(Pow(D(4), m)),
            Add(D(1), Smul(Mul(D(2), Inv(Pow(D(2), m))), Window("czxUnitary", RingSize(m)))))));
    }

    private static Formula DeltaStatement()
    {
        var m = F.Id("m");
        var t = F.Id("t");
        var norm = Call(Quantum + "Foundation.FiniteTraceDistance.traceNorm",
            Sub(Evolved(m, t), Local("stationary", m)));
        return All("m", Naturals(), All("t", Reals(), Eqn(Local("delta", m, t), Div(norm, D(2)))));
    }

    private static Formula EvolutionStatement()
    {
        var m = F.Id("m");
        var t = F.Id("t");
        var x = F.Id("x");
        var word = Growth("word", ExpNeg(t), m, Local("blocks", m, x));
        var coefficient = Call("Complex.ofReal", Mul(Pow(Inv(D(2)), m), Call("Matrix.trace", word)));
        var diagonal = Call("Matrix.diagonal", LambdaOf("x", Config(m), coefficient));
        var value = Smul(Inv(Pow(D(4), m)), Add(D(1),
            Mul(Window("czxUnitary", RingSize(m)), diagonal)));
        return All("m", Naturals(), Imp(Le(D(2), m), All("t", Reals(), Eqn(Evolved(m, t), value))));
    }

    private static Formula BoundStatement()
    {
        var m = F.Id("m");
        var t = F.Id("t");
        var rhs = Mul(D(2), Pow(Div(Growth("growthFactor", ExpNeg(t)), D(2)), m));
        return All("m", Naturals(), Imp(Le(D(2), m), All("t", Reals(),
            Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, t),
                Le(Local("delta", m, t), rhs)))));
    }

    private static Formula Evolved(Formula m, Formula t) =>
        Window("evolution", RingSize(m), t, Local("initial", m));

    private static Formula RingSize(Formula m) => Mul(D(2), m);
    private static Formula Config(Formula m) =>
        new Formula.TypeArrow(P(Call("Fin", RingSize(m))), P(Call("Fin", D(2))));
    private static Formula ExpNeg(Formula t) => Call("Real.exp", Seq(Minus, t));
    private static Formula Local(string name, params Formula[] args) => Call(Prefix.Replace('/', '.') + name, args);
    private static Formula Window(string name, params Formula[] args) =>
        Call(TensorNetworks + "CZXParentLindbladianWindowChannel." + name, args);
    private static Formula Growth(string name, params Formula[] args) =>
        Call(TensorNetworks + "CZXParentLindbladianAnnealedGrowth." + name, args);
    private static Formula Qualified(string name) =>
        Seq(Operatorname, Grp(Seq([.. name.Split('.').SelectMany((part, i) =>
            i == 0 ? new Formula[] { F.Id(part) } : [Dot, F.Id(part)])])));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(string name, Formula type) => P(Seq(F.Id(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, P(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(name, type), Sp, Mapsto, Sp, P(body));
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Add, P(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Subtract, P(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Multiply, P(y));
    private static Formula Smul(Formula x, Formula y) => Seq(P(x), Sp, Cdot, Sp, P(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(P(x), y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Inv(Formula x) => Div(D(1), x);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
