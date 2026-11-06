using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class KingmanEstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive block decompositions, stationary tails and a weak maximal inequality control nonnegative subadditive orbit sequences.",
        H("Estimates for nonnegative subadditive cocycles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stationary-tail"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/KingmanEstimates.ae_tendsto_comp_iterate_div_nat"),
                H("Integrable stationary tails vanish after division by time"),
                StatementSource.FromAuthor(StationaryTailStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("For an arbitrary measurable probability space, a measure-preserving transformation T and a measurable integrable nonnegative real observable phi, the value phi at the nth orbit point divided by n converges to zero almost everywhere. No independence or ergodicity is assumed.")),
                    Paragraph(Text("Integrability makes the sum of the probabilities of integer tail events finite. Measure preservation gives the same probabilities for the corresponding orbit events. The first Borel–Cantelli lemma yields an eventual bound at each reciprocal integer level. Countably many levels and nonnegativity give convergence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-blocks"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/KingmanEstimates.greedy_block_bound"),
                H("Adaptive greedy block bound"),
                StatementSource.FromAuthor(GreedyStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("Let F(k,n) be nonnegative real costs, with F(k,0)=0 and F(k,m+n) at most F(k,m)+F(k+m,n). Let B mark bad starting positions. At every good position assume a block of length between one and N whose cost is at most its length times a fixed nonnegative c.")),
                    Paragraph(Text("For every horizon M, the total cost F(0,M) is bounded by M times c, plus the one-step costs at bad positions before M, plus the one-step costs at positions k before M with M at most k+N. The two sums can overlap, and the bound retains that overlap.")),
                    Paragraph(Text("Strong induction on the remaining length implements the adaptive tiling. A bad position consumes one step and charges its cost to the bad-position sum. A good block that fits is consumed whole and charged to the linear budget. A good block that crosses the horizon consumes one step and charges its cost to the terminal strip. Nonnegativity permits the unused parts of the two sums to be retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weak-maximal"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/KingmanEstimates.measure_kingmanDick_le"),
                H("Weak maximal inequality for invariant divergence sets"),
                StatementSource.FromAuthor(WeakMaximalStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("For a measurable integrable nonnegative phi on a probability space and c>0, the invariant divergence set consists of points whose orbit sums exceed n times some rational level greater than c arbitrarily late. Its measure is at most the integral of phi divided by c, interpreted as a nonnegative extended real.")),
                    Paragraph(Text("Apply the maximal ergodic integral inequality to the indicator of the invariant divergence set times phi-c. Orbit invariance identifies its sums inside the set and makes them zero outside. The resulting nonnegative integral bounds c times the measure of the set by the integral of phi on that set, and then by the full integral."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classical references are Kingman, The ergodic theory of subadditive stochastic processes (1968), and Steele, Kingman's subadditive ergodic theorem (1989). Durrett, Probability: Theory and Examples, fifth edition, Section 6.4, gives the stationary-array theorem. The Lean proof source is facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean, revision a60759060b5616df0d5775b42da4d337719feb32. The Meta Platforms copyright and complete supplier license, including its preface, are retained separately from the citation-only book reference.")))));

    private static Formula V(string name) => name switch
    {
        "alpha" => Alpha,
        "mu" => Mu,
        "phi" => Phi,
        _ => F.Id(name)
    };
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Ae(Formula body) =>
        Call("Eventually", Lam("x", V("alpha"), body), Call("ae", V("mu")));
    private static Formula Orbit(Formula n) => App(Call("iterate", V("T"), n), V("x"));
    private static Formula Space() => Seq(
        All("alpha", Seq(Call("Type"), Sp, V("u"))),
        Instance(Call("MeasurableSpace", V("alpha"))),
        All("mu", Call("Measure", V("alpha"))),
        Instance(Call("IsProbabilityMeasure", V("mu"))),
        All("T", Fn(V("alpha"), V("alpha"))));
    private static Formula Observable() => Seq(
        Call("MeasurePreserving", V("T"), V("mu"), V("mu")), Sp, Rightarrow,
        All("phi", Fn(V("alpha"), Real)),
        Call("Measurable", V("phi")), Sp, Rightarrow,
        Call("Integrable", V("phi"), V("mu")), Sp, Rightarrow,
        Par(Seq(All("x", V("alpha")), D(0), Leq, App(V("phi"), V("x")))),
        Sp, Rightarrow);

    private static Formula StationaryTailStatement() => Disp(new Formula.Aligned([
        Space(), Observable(),
        Ae(Call("Tendsto", Lam("m", Nat,
                Seq(Frac, Grp(App(V("phi"), Orbit(V("m")))), Grp(V("m")))),
            Call("atTop"), Call("nhds", D(0))))
    ]));

    private static Formula Cost(Formula k, Formula n) => App(V("F"), k, n);
    private static Formula SumBefore(Formula summand) =>
        Call("sum", Call("range", V("M")), Lam("k", Nat, summand));
    private static Formula GreedyStatement() => Disp(new Formula.Aligned([
        Seq(All("F", Fn(Nat, Fn(Nat, Real))),
            Par(Seq(All("k", Nat), All("n", Nat), D(0), Leq, Cost(V("k"), V("n")))),
            Sp, Rightarrow),
        Seq(Par(Seq(All("k", Nat), Cost(V("k"), D(0)), Eq, D(0))), Sp, Rightarrow),
        Seq(Par(Seq(All("k", Nat), All("m", Nat), All("n", Nat),
            Cost(V("k"), Seq(V("m"), Plus, V("n"))), Leq,
            Cost(V("k"), V("m")), Plus, Cost(Seq(V("k"), Plus, V("m")), V("n")))),
            Sp, Rightarrow),
        Seq(All("B", Fn(Nat, Call("Prop"))), Instance(Call("DecidablePred", V("B"))),
            All("c", Real), D(0), Leq, V("c"), Sp, Rightarrow, All("N", Nat)),
        Seq(Par(Seq(All("k", Nat), Neg, App(V("B"), V("k")), Sp, Rightarrow,
            Exists, Sp, V("n"), Colon, Nat, Comma, Sp,
            D(1), Leq, V("n"), Land, V("n"), Leq, V("N"), Land,
            Cost(V("k"), V("n")), Leq, V("n"), Cdot, V("c"))), Sp, Rightarrow),
        Seq(All("M", Nat), Cost(D(0), V("M")), Leq, V("M"), Cdot, V("c"), Plus,
            SumBefore(Call("ite", App(V("B"), V("k")), Cost(V("k"), D(1)), D(0))), Plus),
        SumBefore(Call("ite", Seq(V("M"), Leq, V("k"), Plus, V("N")),
            Cost(V("k"), D(1)), D(0)))
    ]));

    private static Formula WeakMaximalStatement() => Disp(new Formula.Aligned([
        Space(), Observable(),
        Seq(All("c", Real), D(0), Lt, V("c"), Sp, Rightarrow,
            App(V("mu"), Call("DickSet", V("T"), V("phi"), V("c"))), Leq,
            Call("ofReal", Seq(Frac, Grp(Call("integral", V("mu"), V("phi"))), Grp(V("c")))))
    ]));
}
