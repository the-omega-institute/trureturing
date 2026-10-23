using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Sandpiles;

internal sealed class UniformClockAvalancheDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Sandpiles/UniformClockAvalanche.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/riihimakismith2026avalanche");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string n) => Seq(Operatorname, Grp(F.Id(n)));
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Named(n), [.. a]);
    private static Formula App(Formula n, params Formula[] a) => new Formula.Apply(n, [.. a]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Some(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Minus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SetOf(Formula a) => Call("Finset", a);
    private static Formula Indicator(Formula p) => Call("ite", p, D(1), D(0));
    private static Formula Generic(Formula body) => All("W", Named("Type"),
        Seq(OpenBracket, Call("Fintype", F.Id("W")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id("W")), CloseBracket, Sp,
        All("G", Call("Digraph", F.Id("W")),
        Seq(OpenBracket, Call("DecidableRel", Call("Adj", F.Id("G"))), CloseBracket, Sp, body))));
    private static DocumentBlock Node(string n, Formula f, string p, bool theorem = false) => Describe.Lean(
        DescribeId.Create("uniform-clock-" + n.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(n.Replace('_', ' ')), StatementSource.FromAuthor(Disp(f)),
        theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(p))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        Formula W = F.Id("W"), G = F.Id("G"), c = F.Id("c"), w = F.Id("w"), a = F.Id("a"), t = F.Id("t"), tau = F.Id("T");
        Formula V = F.Id("V"), m = F.Id("m"), f = F.Id("f"), b = F.Id("b"), i = F.Id("i"), v = F.Id("v");
        Formula d = Call("outdegree", G, w), fire = Call("firing", G, c);
        Formula incoming = Seq(Sum, Underscore, Grp(Mem(a, W)), Sp, Indicator(And(Mem(a, fire), Call("Adj", G, a, w))));
        Formula family = Fn(Call("Fin", m), SetOf(V));
        Formula clockW = Call("Sum", Call("Sum", V, Call("Fin", m)), Named("Unit"));
        Formula clockParams(Formula body) => All("V", Named("Type"),
            Seq(OpenBracket, Call("DecidableEq", V), CloseBracket, Sp, All("m", N, All("F", family, body))));
        Formula facets = Call("facets", F.Id("K"));
        Formula Fs = Call("values", f);
        Formula cg = Call("clockGraph", Fs);
        Formula init = Call("initial", Fs, b);
        Formula ct = Call("orbit", cg, init, t);
        Formula sigma = Call("firing", cg, ct);
        Formula profiles = And(All("t", N, All("v", V,
            Eq(App(ct, Call("original", m, v)), Call("O", Fs, b, t, v)))),
            All("t", N, All("i", Call("Fin", m), Eq(App(ct, Call("clock", i)), Call("P", Fs, t, i)))));
        Formula sets = All("t", N, Eq(sigma, Call("S", Fs, b, t)));
        Formula faces = All("T", SetOf(clockW), Iff(Mem(tau, Call("avalanche", cg, init)),
            And(Call("Nonempty", tau), Or(
                Some("A", SetOf(V), And(Mem(F.Id("A"), F.Id("K")), Eq(tau, Call("map", Call("original", m), F.Id("A"))))),
                Some("i", Call("Fin", m), Subset(tau, Call("insert", Call("clock", i), Call("map", Call("original", m), Call("B", Fs, b, i)))))))));
        Formula result = All("V", Named("Type"), Seq(
            OpenBracket, Call("Fintype", V), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", V), CloseBracket, Sp,
            All("K", Call("AbstractSimplicialComplex", V), All("m", N, Imp(Le(D(1), m),
            All("f", Fn(Call("Fin", m), facets), Imp(Call("Surjective", f),
            All("b", V, And(profiles, And(sets, faces))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A clock for each ordered maximal face realizes every finite complex without ghost original vertices as the original slice of an actual parallel avalanche. The orbit is classified for every natural time, including its final facet and its empty firing tail.",
            H("Uniform all-time clock avalanche"), Blocks(
                Node("outdegree", Generic(All("w", W, Eq(d, Call("card", Call("filter", Call("Adj", G, w), Call("univ", W)))))),
                    "Out-degree counts actual outgoing arcs."),
                Node("firing", Generic(All("c", Fn(W, N), All("w", W,
                    Iff(Mem(w, fire), And(Lt(D(0), d), Le(d, App(c, w))))))),
                    "Every unstable vertex with positive out-degree fires once. This excludes all sinks even when they have accumulated grains."),
                Node("step", Generic(All("c", Fn(W, N), All("w", W,
                    Eq(Call("step", G, c, w), Add(Minus(App(c, w), Call("ite", Mem(w, fire), d, D(0))), incoming))))),
                    "Subtraction uses eligibility in the old configuration, followed by one arrival along each arc from the old complete firing set. Arrivals cannot authorize same-time firing; sink coordinates are retained."),
                Node("orbit", Generic(All("c", Fn(W, N), All("t", N,
                    Eq(Call("orbit", G, c, t), Call("iterate", Call("step", G), t, c))))),
                    "The actual orbit iterates the synchronous transition; no firing schedule is an input."),
                Node("avalanche", Generic(All("c", Fn(W, N), All("T", SetOf(W),
                    Iff(Mem(tau, Call("avalanche", G, c)), And(Call("Nonempty", tau),
                        Some("t", N, Subset(tau, Call("firing", G, Call("orbit", G, c, t))))))))),
                    "The native complex omits the empty face and takes the downward closure of actual firing sets at all natural times. Conventional augmentation adds only the empty face."),
                Node("original", All("V", Named("Type"), All("m", N, All("v", V,
                    Eq(Call("original", m, v), Call("inl", Call("inl", v)))))),
                    "Originals embed into the first summand of W = (V + Fin m) + Unit. Clock i is inl(inr i); the sink is inr(unit)."),
                Node("neighbours", clockParams(All("w", clockW,
                    Eq(Call("neighbours", F.Id("F"), w), Call("N", F.Id("F"), w)))),
                    "N(F,o(v)) is the sink singleton. N(F,p(i)) is o[F(i)] together with p(i+1) when i+1<m and the sink otherwise. N(F,s) is empty. Distinct summands exclude loops and separate the successor from the facet."),
                Node("clockGraph", clockParams(All("a", clockW, All("w", clockW,
                    Iff(Call("Adj", Call("clockGraph", F.Id("F")), a, w), Mem(w, Call("neighbours", F.Id("F"), a)))))),
                    "Adjacency is membership in the actual outgoing neighbor set. Original out-degree is one; clock out-degree is the facet cardinality plus one; sink out-degree is zero."),
                Node("initial", clockParams(All("b", V, All("w", clockW,
                    Eq(Call("initial", F.Id("F"), b, w), Call("C", F.Id("F"), b, w))))),
                    "C(F,b,o(v)) is one exactly at b. C(F,b,p(i)) is |F(i)| + [i=0]. C(F,b,s)=0. No restriction on facet overlap, repetition, order, or the choice of b is imposed."),
                Node("uniform_clock_all_time", result,
                    "Here F(i) is the underlying maximal face of f(i), and f is an arbitrary surjective ordered enumeration, permitting repetitions. O(F,b,0,v)=[v=b]; O(F,b,t,v)=[v in F(t-1)] for 1<=t<=m and zero thereafter. P(F,t,i)=|F(i)| for t<i, |F(i)|+1 for t=i, and zero for t>i. S(F,b,0)={o(b),p(0)}; S(F,b,t)=o[F(t-1)] union {p(t)} for 1<=t<m; S(F,b,m)=o[F(m-1)]; S(F,b,t) is empty for t>m. B(F,b,0)={b}, and B(F,b,i)=F(i-1) for i>0. The induction removes the current original indicator, replaces it by the active clock's facet indicator, and passes one grain only to the successor clock. At the last facet all clocks are zero; at every later time all nonsinks are zero, while the sink retains its accumulated grains. Maximal-face coverage identifies the original faces with K and the remaining generators with the clock attachment simplices. Every face containing the sink or two clocks is excluded. No topology, collapse, homology, or torsion conclusion is included.", true)), []));
    }
}
