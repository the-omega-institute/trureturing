using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class SpinCoupledEvenHypercubeGroverFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/wang2026hypercubelocalization");


    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every even dimension d at least four, the all-plus spin-coupled Grover operator has a nonzero fixed vector with nonconstant position weights. A product of signed coordinate-pair indicators supplies an explicit vector on three adjacent Hamming layers.",
        H("A nonuniform fixed point on every even hypercube"),
        Blocks(
            Node("sign", "The paired sign function", SignFormula(),
                "The equivalence finProdFinEquiv followed by finCongr (Nat.mul_comm m 2) sends (j, b) to coordinate 2j + b. Finsets are coerced to sets in Set.indicator. The function (1 : Fin (2*m) -> Complex) is the constant function one, so each factor is the indicator of coordinate 2j minus that of coordinate 2j+1. The product is zero unless the vertex contains exactly one coordinate from each pair.",
                "f", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("vector", "The three-layer amplitudes", VectorFormula(),
                "The parameters z and c are arbitrary complex numbers in this definition. The operation ite is Lean's conditional; the first test has priority, followed by the lower and upper layer tests. Here m-1 is subtraction in the natural numbers, hence is truncated at zero. For m at least two and z^(2*m)=-1, m*(1+z)*c=1, the sum of the coin amplitudes at a vertex equals f, and the amplitudes satisfy the edge recurrence. The same z and c are used on every layer.",
                "u", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("coefficient", "The amplitude coefficient", CoefficientFormula(),
                "Here z is PositivePauliClockOrder.scalarPhase 1 (Real.pi/(2*m)) 1, the phase exp(-i*pi/(2*m)). For m at least two, the real part of this phase is cos(pi/(2*m)) and is positive. Thus 1+z is nonzero, and c(m) is nonzero and satisfies m*(1+z)*c(m)=1. All division here is division in Complex.",
                "c", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("operator", "The all-plus reduced Grover operator", OperatorFormula(),
                "Section 3, page 6, Proposition 3.4 defines the reduced evolution operator; Section 4, page 12, specifies C_k = (2/d) sum_j |e_k><e_j| - |e_k><e_k| and phi_sigma = |sigma|*pi/d. The all-plus restriction acts at output vertex t and coin coordinate k through predecessor symmDiff t {k}. The phase uses the predecessor's cardinality. The position carrier Finset (Fin d) enumerates all vertices and Fin d enumerates the d coin coordinates. The Grover coin contribution is (2/d) times the sum of all predecessor coin amplitudes, minus the kth predecessor amplitude. The casts to Complex and the anonymous summation index are shown explicitly.",
                "W", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Wang's conjecture", ClaimFormula(),
                "The predicate claim encodes the source's equivalent fixed-point clause. The letters v, s and t denote the coin-amplitude family and two vertices. Its position weight at s is the real sum of squared complex norms; dividing all weights by the total nonzero squared norm preserves their inequality. There is no extra hypothesis on the dimension or the vector.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The fixed-point clause holds", Disp(F.Id("claim")),
                "Write d=2*m with m at least two, put z=PositivePauliClockOrder.scalarPhase 1 (Real.pi/(2*m)) 1, and take u(m, z, c(m)). Pair cancellation makes the sum of f over all one-coordinate neighbours zero, while f vanishes off the middle layer. These facts give sum_k u(s,k)=f(s). The middle, lower and upper layer branches satisfy z^|s|*((1/m)*f(s)-u(s,k))=u(symmDiff s {k},k); the remaining branches vanish. Since z^(2*m)=-1, this is exactly W u=u. At the vertex containing all even coordinates, f=1 and an even-coordinate amplitude is c(m), which is nonzero; all amplitudes at the empty vertex vanish. Hence the first position weight is strictly positive and the second is zero. Page 11, Corollary 4.4 (cor:fixed_point_DFL) then implies disorder-free localization by normalizing the fixed point. This last implication uses the paper's spectral criterion; the displayed Lean proposition is the equivalent fixed-point clause.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("wang-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(formula), provenance,
        declaration == "claim" ? Blocks(SourceQuotation(), Paragraph(Text(prose))) : Blocks(Paragraph(Text(prose))), role,
        declaration == "result" ? new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("wang-2026-hypercube-disorder-free-localization"),
            ResolutionKind.Proved) : null);

    private static DocumentBlock SourceQuotation() => Paragraph(
        Text("Page 13, Conjecture 4.1: \"For every even "),
        Math(Seq(F.Id("d"), Sp, Geq, Sp, D(4))),
        Text(", the spin-coupled Grover walk on the "), Math(F.Id("d")),
        Text("-dimensional hypercube with coupling "),
        Math(Eq(new Formula.Subscript(Phi, SigmaLower),
            Seq(Lvert, SigmaLower, Rvert, Pi, Slash, F.Id("d")))),
        Text(" and all "), Math(Seq(Plus, D(1))),
        Text(" spin configuration exhibits disorder-free localization. Equivalently, the reduced evolution operator "),
        Math(new Formula.Subscript(Seq(Widetilde, Grp(F.Id("W"))), Seq(Mathbf, Grp(F.Id("s"))))),
        Text(" possesses a fixed point whose position distribution is non-uniform.\""));

    private static Formula BbN => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BbC => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name) => name.Contains('_')
        ? Seq(Operatorname, Grp(F.Id(name.Split('_')[0])), Underscore, Grp(F.Id(name.Split('_')[1])))
        : Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula name, params Formula[] arguments) =>
        new Formula.Apply(name, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Vertices(Formula d) => Call("Finset", Fin(d));
    private static Formula State(Formula d) => Seq(Vertices(d), Sp, To, Sp, Fin(d), Sp, To, Sp, BbC);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Card(Formula s) => Apply(Qualified("Finset", "card"), s);
    private static Formula Toggle(Formula s, Formula k) => Call("symmDiff", s, new Formula.SetLiteral([k]));
    private static Formula Member(Formula k, Formula s) => new Formula.Relation(k, FormulaRelationOperator.MemberOf, s);
    private static Formula SumOver(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Colon, Sp, type)), Sp, body);
    private static Formula Mass(Formula v, Formula s, Formula d) =>
        SumOver("k", Fin(d), Pow(new Formula.Norm(Apply(v, s, F.Id("k"))), D(2)));

    private static Formula SignFormula()
    {
        Formula m = F.Id("m"), s = F.Id("s"), j = F.Id("j");
        Formula dim = Mul(D(2), m);
        Formula equivalence = Apply(Seq(Named("finProdFinEquiv"), Dot, Named("trans")),
            Call("finCongr", Apply(Qualified("Nat", "mul_comm"), m, D(2))));
        Formula coord(Formula b) => Apply(equivalence, Parenthesized(Seq(j, Comma, Sp, b)));
        Formula indicator(Formula b) => Apply(Qualified("Set", "indicator"), Cast(s, Call("Set", Fin(dim))),
            Cast(D(1), Seq(Fin(dim), Sp, To, Sp, BbC)), coord(b));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(j, Colon, Sp, Fin(m))), Sp,
            Parenthesized(Sub(indicator(D(0)), indicator(D(1)))));
        return Disp(All("m", BbN, All("s", Vertices(dim), Eq(Call("f", m, s), product))));
    }

    private static Formula VectorFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), c = F.Id("c"), s = F.Id("s"), k = F.Id("k");
        Formula mid = Eq(Card(s), m);
        Formula low = And(Eq(Card(s), Sub(m, D(1))), new Formula.Not(Parenthesized(Member(k, s))));
        Formula high = And(Eq(Card(s), Add(m, D(1))), Member(k, s));
        Formula middle = Call("ite", Parenthesized(Member(k, s)), Mul(c, Call("f", m, s)),
            Mul(Mul(z, c), Call("f", m, s)));
        Formula lower = Mul(Mul(Pow(z, Add(m, D(1))), c), Call("f", m, Toggle(s, k)));
        Formula upper = Mul(Mul(Pow(z, m), c), Call("f", m, Toggle(s, k)));
        Formula body = Call("ite", Parenthesized(mid), middle,
            Call("ite", Parenthesized(low), lower, Call("ite", Parenthesized(high), upper, D(0))));
        return Disp(All("m", BbN, All("z", BbC, All("c", BbC,
            All("s", Vertices(Mul(D(2), m)), All("k", Fin(Mul(D(2), m)),
                Eq(Call("u", m, z, c, s, k), body)))))));
    }

    private static Formula CoefficientFormula()
    {
        Formula m = F.Id("m");
        return Disp(All("m", BbN, Eq(Call("c", m), new Formula.Fraction(D(1),
            Mul(Cast(m, BbC), Parenthesized(Add(D(1), Apply(Qualified("PositivePauliClockOrder", "scalarPhase"), D(1),
                new Formula.Fraction(Qualified("Real", "pi"), Cast(Mul(D(2), m), Seq(Mathbb, Grp(F.Id("R"))))), D(1)))))))));
    }

    private static Formula OperatorFormula()
    {
        Formula d = F.Id("d"), v = F.Id("v"), t = F.Id("t"), k = F.Id("k");
        Formula pred = Toggle(t, k);
        Formula angle = new Formula.Negate(new Formula.Fraction(
            Mul(Cast(Qualified("Real", "pi"), BbC), Cast(Card(pred), BbC)), Cast(d, BbC)));
        Formula phase = Apply(Qualified("Complex", "exp"), Mul(angle, Qualified("Complex", "I")));
        Formula sum = SumOver("j", Fin(d), Apply(v, pred, F.Id("j")));
        Formula coin = Sub(Mul(new Formula.Fraction(D(2), Cast(d, BbC)), Parenthesized(sum)), Apply(v, pred, k));
        return Disp(All("d", BbN, All("v", State(d), All("t", Vertices(d), All("k", Fin(d),
            Eq(Call("W", d, v, t, k), Mul(phase, Parenthesized(coin))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), v = F.Id("v"), s = F.Id("s"), t = F.Id("t");
        Formula unequal = Ex("s", Vertices(d), Ex("t", Vertices(d), Ne(Mass(v, s, d), Mass(v, t, d))));
        Formula witness = Ex("v", State(d), And(Ne(v, D(0)), And(Eq(Call("W", d, v), v), unequal)));
        Formula body = All("d", BbN, Imp(Call("Even", d),
            Imp(new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, d), witness)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
