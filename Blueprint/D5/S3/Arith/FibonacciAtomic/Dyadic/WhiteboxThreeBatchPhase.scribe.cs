using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Dyadic;

internal sealed class WhiteboxThreeBatchPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.";
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula t, Formula b) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Ex(Formula x, Formula t, Formula b) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula Frac(Formula a, int b) => new Formula.Fraction(a, D(b));
    private static Formula Times(int a, Formula b) =>
        Seq(D(a.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(c => c - '0').ToArray()), Sp, b);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));

    public DocumentDefinition Create()
    {
        var n = V("N"); var l = V("lambda"); var s = V("s");
        var sharp = Call("sharp", n, l);
        Formula G(string name) => Call(name, n, l);
        var first = Times(17, n);
        var middle = Seq(Frac(Times(67, n), 4), Sp, Plus, Sp, Frac(Times(3, l), 2));
        var last = Seq(Frac(Times(50, n), 3), Sp, Plus, Sp, Frac(Times(8, l), 3));
        var samplers = Call("PrefixSampler", V("Strategy"));
        var attainG = Ex(s, samplers, And(Call("Coarse", s),
            Equal(Call("G", s, n, l), Call("ofReal", sharp))));
        var attainH = Ex(s, samplers, And(Call("Coarse", s),
            Equal(Call("H", s, n, l), Call("ofReal", first))));
        var conclusion = And(Equal(G("rawGamma"), Call("ofReal", sharp)),
            Equal(G("coarseGamma"), Call("ofReal", sharp)), attainG,
            Imp(Seq(n, Sp, Le, Sp, Times(6, l)), Equal(G("rawGamma"), Call("ofReal", first))),
            Imp(Seq(Times(6, l), Sp, Le, Sp, n), Imp(Seq(n, Sp, Le, Sp, Times(14, l)),
                Equal(G("rawGamma"), Call("ofReal", middle)))),
            Imp(Seq(Times(14, l), Sp, Le, Sp, n), Equal(G("rawGamma"), Call("ofReal", last))),
            Equal(G("rawH"), Call("ofReal", first)),
            Equal(G("coarseH"), Call("ofReal", first)), attainH);
        var statement = All(n, Nat, Imp(Seq(D(1), Sp, Le, Sp, n), All(l, Real,
            Imp(Seq(D(0), Sp, Lt, Sp, l), conclusion))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A once-paid fair-bit choice of a total tree controller has three exact batch phases.",
            H("Three-tree Paid Batch Phase"), Blocks(
                Paragraph(Text("The evaluated trees are the k=1 family from Scale36ActualEndpointAcquisition, "
                    + "ordered as P0, U1, V1. A Strategy is correct and finitely terminating on every "
                    + "finite labelled source tree, with no promise about prototype identity or size. "
                    + "A sampler chooses this complete strategy before any input arrives. The chosen "
                    + "strategy is shared by every counterfactual tuple and by all N runs, each run "
                    + "starting from an empty real-address cache. Internal computation and address length "
                    + "are unpriced; every consumed fair bit costs lambda and every distinct acquired "
                    + "address in a run costs one. The coarse class requires every emitted policy to "
                    + "factor through the merged-nonleaf history interface.")),
                Paragraph(Text("For a tape t and a tuple q in Fin(N)->Fin(3), paidTuple is "
                    + "lambda times the bit bill plus the sum of the N controller costs on the "
                    + "selected prototypes. G is the maximum over fixed tuples of the expected paidTuple. "
                    + "H takes this maximum separately on each tape before expectation. rawGamma and "
                    + "rawH take infima over all input-independent almost-surely stopping prefix samplers; "
                    + "coarseGamma and coarseH restrict to coarse samplers. Expectations and infima use "
                    + "nonnegative extended reals, so infinite expected bit costs remain included.")),
                MathBlock(Disp(All(n, Nat, All(l, Real,
                    Equal(sharp, Call("min", first, Call("min", middle, last))))))),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Exact values, thresholds, and attained infima"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every N at least one and positive lambda, both interfaces "
                        + "have the displayed sharp value. The deterministic, biased, and uniform laws "
                        + "give its three lines, switching at N=6 lambda and N=14 lambda. The boundary "
                        + "formulas agree, and a coarse sampler attains each infimum. Taking the "
                        + "maximum before expectation instead has sharp attained value 17N.")),
                        Paragraph(Text("Every controller dominates one profile with cost 16 at one "
                        + "prototype and 17 at the other two. Restricting a splitting recipe to a "
                        + "nonempty subset preserves an upper bound on its excess, and the existing "
                        + "root-excess theorem excludes two zero-excess members. Relabelling a sampled "
                        + "controller by its dominated profile preserves the full original bit bill. "
                        + "If p is the resulting common profile law and t its smallest coordinate, "
                        + "a constant input tuple gives cost at least N(17-t)+lambda L(p). "
                        + "The universal prefix-cylinder bound connects the actual bill to L(p); "
                        + "the existing Mersenne supporting lines give L(p)>=6t and L(p)>=14t-2.")),
                        Paragraph(Text("The point law emits a coarse endpoint at the empty word and "
                        + "pays zero bits. A finite three-leaf code has probabilities 1/2,1/4,1/4 "
                        + "and expected length 3/2. A finite-state two-level repeating code gives "
                        + "equal probabilities 1/3 and expected length 8/3. Their stopping words "
                        + "are realized through the public fixed-label carry-tree contract. "
                        + "On every tape some prototype costs at least 17, while a point endpoint "
                        + "costs at most 17 on each prototype, which proves the value for H.")),
                        Paragraph(Text("The dyadic random-bit cost is classical Knuth-Yao theory, "
                        + "as recalled in Lumbroso, Section 2.1. The complete tree-controller "
                        + "optimization and its raw and coarse batch comparison are repository results."))),
                    DescribeRole.Theorem))));
    }
}
