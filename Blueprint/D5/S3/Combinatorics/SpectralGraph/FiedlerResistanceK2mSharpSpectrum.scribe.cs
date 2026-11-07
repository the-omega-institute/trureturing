using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FiedlerResistanceK2mSharpSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp product equality on labelled K2m determines the entire native spectrum.",
        H("The sharp product and its two positive spectral rays"),
        Blocks(
            Paragraph(Text("Every natural m at least three is allowed. The vertices are Fin (2+m), with two labelled hubs and m labelled leaves. Every one of the 2m hub-to-leaf conductances varies independently over strictly positive reals. The matrix is the original ordinary unnormalized wLap, lambda2 is the original mean-zero Rayleigh infimum, and totalRes is the original harmonic-current resistance summed over every unordered distinct vertex pair, including nonadjacent pairs. No total-conductance or symmetry assumption is imposed on competitors. Nonedge values are arbitrary.")),
            Node("spectrum", "The complete native eigenvalue multiplicities", "FullSpectrum",
                "The eigenvalues are those returned by Matrix.IsHermitian.eigenvalues for the actual matrix wLap (K2m m) w. FullSpectrum requires exactly one zero eigenvalue, exactly m entries equal to t, exactly one entry equal to m*t, and every entry equal to one of those three values. It imposes no ascending-index convention and introduces no surrogate matrix or assumed spectral list. When m is at least three and t is positive, the three values are distinct. The generic Hermitian spectral theorem makes this indexed enumeration the full spectrum with multiplicity.", DescribeRole.Definition),
            Node("ray", "One common sign across every leaf", "Ray",
                "For a real scale t and sign epsilon, Ray fixes each first-hub conductance to t/2*(1+epsilon*sqrt((m-2)/(m+2))) and each second-hub conductance to t/2*(1-epsilon*sqrt((m-2)/(m+2))). The same epsilon is used for all leaves. The theorem restricts t to positive values and epsilon to +1 or -1. The definition compares only labelled edges.", DescribeRole.Definition),
            Node("claim", "The whole sharp-product endpoint", "SharpProductClaim",
                "The conjunction contains the universal product bound C_m=(m+2)(m+1/m); equality if and only if a positive scale and one common sign give the edge restriction; existence and positivity of both rays at every positive scale; lambda2=t, totalRes=C_m/t and the full native spectrum on every such restriction; disjointness of the two labelled rays even when their positive scales differ; interchange of the rays under hub exchange; and invariance of lambda2 and totalRes under arbitrary changes on nonedges. Applying the equality characterization and the universal ray conclusion gives the complete spectrum at every equality case.", DescribeRole.Definition),
            Node("result", "The sharp bound, all equality restrictions and their full spectra", "result",
                "The product bound, trace equality, positive spectral lower bound, harmonic reciprocal-eigenvalue formula, zero multiplicity, equality parameters, quadratic parameter roots and extremal lambda2/resistance values are direct applications of the original frozen optimizer suppliers. The additional argument proves reciprocal equality rigidity: for the m+1 positive native eigenvalues r_i, put q_i=r_i/t-1. Trace equality gives sum q_i=m-1. Each difference q_i/(1+q_i)-q_i/m is nonnegative, and product equality makes their sum zero. Hence each q_i is either zero or m-1; a positive total forces exactly one nonzero term. Consequently exactly one native eigenvalue is m*t and exactly m are t. This relation is used for every positive point on either equality ray. The construction remains on the original native matrix and harmonic resistance carriers throughout. These are repository-derived consequences of the selected K2m theory; no literature novelty or external open-problem resolution is asserted.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string name, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fks-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string x) => StrataLint.Scribe.FormulaDsl.Id(x);
    private static Formula C(string x) => new Formula.NamedConstant(FormulaIdentifier.Create(x));
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula ty, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), ty, b);
    private static Formula Ex(string n, Formula ty, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), ty, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Not(Formula a) => new Formula.Not(Par(a));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Neg(Formula a) => Seq(Minus, Par(a));
    private static Formula W() => Seq(Call("Sym2", Call("Fin", Add(D(2), V("m")))), Sp, To, Sp, C("Real"));
    private static Formula G() => Call("K2m", V("m"));
    private static Formula L(Formula w) => Call("lambda2", G(), w);
    private static Formula R(Formula w) => Call("totalRes", G(), w);
    private static Formula Sharp() => Call("sharpConstant", V("m"));
    private static Formula Positive(Formula w) => All("e", Call("Sym2", Call("Fin", Add(D(2), V("m")))),
        Imp(In(V("e"), Call("edgeSet", G())), Lt(D(0), App(w, V("e")))));
    private static Formula Ray(Formula t, Formula sign, Formula w) => Call("Ray", V("m"), t, sign, w);
    private static Formula Signs(Formula sign) => Or(Eqn(sign, D(1)), Eqn(sign, Neg(D(1))));
    private static Formula Spectrum(Formula w, Formula t) => Call("FullSpectrum", V("m"), w, t);
    private static Formula Exchange(Formula w) => Call("exchangeWeights", V("m"), w);
    private static Formula Edges(Formula w, Formula v) => All("e", Call("Sym2", Call("Fin", Add(D(2), V("m")))),
        Imp(In(V("e"), Call("edgeSet", G())), Eqn(App(w, V("e")), App(v, V("e")))));
    private static Formula Count(Formula x) => Call("card", Call("filter", Par(Seq(LambdaLower, Sp, V("i"), Sp, Mapsto, Sp,
        Eqn(App(V("e"), V("i")), x))), Call("univ", Call("Fin", Add(D(2), V("m"))))));
    private static Formula SpectrumBody() => And(Eqn(Count(D(0)), D(1)), And(Eqn(Count(V("t")), V("m")),
        And(Eqn(Count(Mul(V("m"), V("t"))), D(1)), All("i", Call("Fin", Add(D(2), V("m"))),
            Or(Eqn(App(V("e"), V("i")), D(0)), Or(Eqn(App(V("e"), V("i")), V("t")), Eqn(App(V("e"), V("i")), Mul(V("m"), V("t")))))))));
    private static Formula Conclusion()
    {
        Formula w = V("w"), wp = V("wprime"), t = V("t"), sign = V("epsilon");
        Formula bound = All("w", W(), Imp(Positive(w), Leq(Mul(L(w), R(w)), Sharp())));
        Formula classification = All("w", W(), Imp(Positive(w), Iff(Eqn(Mul(L(w), R(w)), Sharp()),
            Ex("t", C("Real"), Ex("epsilon", C("Real"), And(Lt(D(0), t), And(Signs(sign), Ray(t, sign, w))))))));
        Formula facts = All("t", C("Real"), All("epsilon", C("Real"), Imp(Lt(D(0), t), Imp(Signs(sign),
            And(Ex("w", W(), Ray(t, sign, w)), All("w", W(), Imp(Ray(t, sign, w), And(Positive(w),
                And(Eqn(L(w), t), And(Eqn(R(w), Div(Sharp(), t)), Spectrum(w, t)))))))))));
        Formula distinct = Not(Ex("t", C("Real"), Ex("s", C("Real"), Ex("w", W(),
            And(Lt(D(0), t), And(Lt(D(0), V("s")), And(Ray(t, D(1), w), Ray(V("s"), Neg(D(1)), w))))))));
        Formula exchange = All("t", C("Real"), All("epsilon", C("Real"), All("w", W(),
            Imp(Ray(t, sign, w), Ray(t, Neg(sign), Exchange(w))))));
        Formula nonedges = All("w", W(), All("wprime", W(), Imp(Edges(w, wp),
            And(Eqn(L(w), L(wp)), Eqn(R(w), R(wp))))));
        return And(bound, And(classification, And(facts, And(distinct, And(exchange, nonedges)))));
    }
    private static Formula Statement(string name) => name switch
    {
        "FullSpectrum" => All("m", C("Nat"), All("w", W(), All("t", C("Real"),
            Iff(Spectrum(V("w"), V("t")),
                Seq(V("let"), Sp, V("e"), Sp, Colon, Eq, Sp, Call("eigenvalues", Call("wLap", G(), V("w"))), Sp, V("in"), Sp, SpectrumBody()))))),
        "Ray" => All("m", C("Nat"), All("t", C("Real"), All("epsilon", C("Real"), All("w", W(),
            Iff(Ray(V("t"), V("epsilon"), V("w")), Call("EdgeRestriction", V("m"),
                Mul(Div(V("t"), D(2)), Add(D(1), Mul(V("epsilon"), Call("splitRatio", V("m"))))),
                Mul(Div(V("t"), D(2)), Sub(D(1), Mul(V("epsilon"), Call("splitRatio", V("m"))))), V("w"))))))),
        "SharpProductClaim" => All("m", C("Nat"), Iff(Call("SharpProductClaim", V("m")), Conclusion())),
        "result" => All("m", C("Nat"), Imp(Leq(D(3), V("m")), Conclusion())),
        _ => throw new System.InvalidOperationException("Unknown source declaration.")
    };
}
