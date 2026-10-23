using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Dyadic;

internal sealed class WhiteboxFiveBatchPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase.";
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula t, Formula b) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Ex(Formula x, Formula t, Formula b) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, t, Comma, Sp, b));
    private static Formula Digits(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Frac(Formula a, int b) => new Formula.Fraction(a, Digits(b));
    private static Formula Times(int a, Formula b) => Seq(Digits(a), Sp, b);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));

    private static Formula Word(string bits) =>
        Call("word", D(bits.Select(c => (byte)(c - '0')).ToArray()));
    private static Formula Words(params (string Bits, int Label)[] words) =>
        Call("list", words.Select(w => Call("emit", Word(w.Bits), Digits(w.Label))).ToArray());
    private static Formula CodesFormula()
    {
        var b = V("biasedFive"); var u = V("uniformFive"); var d = V("d"); var i = V("i");
        Formula Stops(Formula path, int depth) => Call("stopping", D(5), path, Digits(depth));
        Formula Quarter(int depth) => Call("rotateLabels", Stops(b, depth), V("rotate"));
        Formula Continue(Formula path) => Call("continuing", D(5), path, D(4));
        var bs = Call("relabel", V("rotate"), Call("fromPath", D(5), b));
        var us = Call("fromPath", D(5), u);
        return And(
            Equal(Quarter(1), Words(("00", 0))),
            Equal(Quarter(2), Words(("010", 1), ("011", 2), ("100", 3), ("101", 4))),
            Equal(Quarter(3), Words(("1100", 1), ("1101", 2), ("1110", 3), ("1111", 4))),
            Equal(Continue(b), Seq(OpenBracket, CloseBracket)),
            Equal(Stops(u, 2), Words(("000", 0), ("001", 1), ("010", 2), ("011", 3), ("100", 4))),
            Equal(Stops(u, 3), Words(("1010", 0), ("1011", 1), ("1100", 2), ("1101", 3), ("1110", 4))),
            Equal(Continue(u), Call("list", Word("1111"))),
            All(d, Nat, And(
                Equal(Call("state", u, Seq(d, Sp, Plus, Sp, D(4))), Call("state", u, d)),
                Equal(Call("action", u, Seq(d, Sp, Plus, Sp, D(4))), Call("action", u, d)))),
            All(i, Call("Fin", D(5)), Equal(Call("law", bs, i),
                Call("if", Equal(i, D(0)), Frac(D(1), 4), Frac(D(3), 16)))),
            All(i, Call("Fin", D(5)), Equal(Call("law", us, i), Frac(D(1), 5))),
            Equal(Call("E", Call("bill", bs)), Call("ofReal", D(3))),
            Equal(Call("E", Call("bill", us)), Call("ofReal", Frac(Digits(18), 5))));
    }

    public DocumentDefinition Create()
    {
        var n = V("N"); var l = V("lambda"); var s = V("s");
        var sharp = Call("sharp", n, l);
        Formula G(string name) => Call(name, n, l);
        var first = Times(22, n);
        var middle = Seq(Frac(Times(349, n), 16), Sp, Plus, Sp, Times(3, l));
        var last = Seq(Frac(Times(109, n), 5), Sp, Plus, Sp, Frac(Times(18, l), 5));
        var samplers = Call("PrefixSampler", V("Strategy"));
        var attainG = Ex(s, samplers, And(Call("Coarse", s),
            Equal(Call("G", s, n, l), Call("ofReal", sharp))));
        var attainH = Ex(s, samplers, And(Call("Coarse", s),
            Equal(Call("H", s, n, l), Call("ofReal", first))));
        var conclusion = And(Equal(G("rawGamma"), Call("ofReal", sharp)),
            Equal(G("coarseGamma"), Call("ofReal", sharp)), attainG,
            Imp(Seq(n, Sp, Le, Sp, Times(16, l)), Equal(G("rawGamma"), Call("ofReal", first))),
            Imp(Seq(Times(16, l), Sp, Le, Sp, n), Imp(Seq(n, Sp, Le, Sp, Times(48, l)),
                Equal(G("rawGamma"), Call("ofReal", middle)))),
            Imp(Seq(Times(48, l), Sp, Le, Sp, n), Equal(G("rawGamma"), Call("ofReal", last))),
            Equal(G("rawH"), Call("ofReal", first)),
            Equal(G("coarseH"), Call("ofReal", first)), attainH);
        var statement = All(n, Nat, Imp(Seq(D(1), Sp, Le, Sp, n), All(l, Real,
            Imp(Seq(D(0), Sp, Lt, Sp, l), conclusion))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A once-paid fair-bit choice of a total tree controller has three exact batch phases.",
            H("Five-tree Paid Batch Phase"), Blocks(
                Paragraph(Text("The evaluated trees are the k=2 family from Scale36ActualEndpointAcquisition, "
                    + "ordered as P0, U1, V1, U2, V2. A Strategy is correct and finitely terminating on every "
                    + "finite labelled source tree, with no promise about prototype identity or size. "
                    + "A sampler chooses this complete strategy before any input arrives. The chosen "
                    + "strategy is shared by every counterfactual tuple and by all N runs, each run "
                    + "starting from an empty real-address cache. Internal computation and address length "
                    + "are unpriced; every consumed fair bit costs lambda and every distinct acquired "
                    + "address in a run costs one. The coarse class requires every emitted policy to "
                    + "factor through the merged-nonleaf history interface.")),
                Paragraph(Text("For a tape t and a tuple q in Fin(N)->Fin(5), paidTuple is "
                    + "lambda times the bit bill plus the sum of the N controller costs on the "
                    + "selected prototypes. G is the maximum over fixed tuples of the expected paidTuple. "
                    + "H takes this maximum separately on each tape before expectation. rawGamma and "
                    + "rawH take infima over all input-independent almost-surely stopping prefix samplers; "
                    + "coarseGamma and coarseH restrict to coarse samplers. Expectations and infima use "
                    + "nonnegative extended reals, so infinite expected bit costs remain included.")),
                new DocumentBlock.DisplayFormula(All(n, Nat, All(l, Real,
                    Equal(sharp, Call("min", first, Call("min", middle, last)))))),
                Describe.Lean(DescribeId.Create("code-claim"), DeclarationHandle.Create(Prefix + "CodeClaim"),
                    H("Literal attaining codes"),
                    StatementSource.FromAuthor(Disp(Equal(Call("CodeClaim"), CodesFormula()))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Stopping at depth d returns words of length d+1. "
                        + "The quarter code rotates the carry labels by one modulo five. "
                        + "The uniform path repeats both its state and its action every four depths. "
                        + "Expectations use the common fair-tape measure."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Exact values, thresholds, and attained infima"),
                    StatementSource.FromAuthor(Disp(And(Call("CodeClaim"), statement))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                    Blocks(Paragraph(Text("For every N at least one and positive lambda, both interfaces "
                        + "have the displayed sharp value. The deterministic, biased, and uniform laws "
                        + "give its three lines, switching at N=16 lambda and N=48 lambda. The boundary "
                        + "formulas agree, and a coarse sampler attains each infimum. Taking the "
                        + "maximum before expectation instead has sharp attained value 22N.")),
                        Paragraph(Text("Every controller dominates one profile with cost 21 at one "
                        + "prototype and 22 at the other four. Restricting a splitting recipe to a "
                        + "nonempty subset preserves an upper bound on its excess, and the existing "
                        + "root-excess theorem excludes two zero-excess members. Relabelling a sampled "
                        + "controller by its dominated profile preserves the full original bit bill. "
                        + "If p is the resulting common profile law and t its smallest coordinate, "
                        + "a constant input tuple gives cost at least N(22-t)+lambda L(p). "
                        + "The universal prefix-cylinder bound connects the actual bill to L(p); "
                        + "the existing five-outcome supporting lines give L(p)>=16t and L(p)>=48t-6.")),
                        Paragraph(Text("The point law emits a coarse endpoint at the empty word and "
                        + "pays zero bits. A finite five-result code emits 0 on 00, emits 1 through 4 on "
                        + "010,011,100,101, and again emits 1 through 4 on 1100,1101,1110,1111. "
                        + "Its law is (1/4,3/16,3/16,3/16,3/16), with expected length 3. "
                        + "The uniform code emits 0 through 4 on 000,001,010,011,100 and "
                        + "on 1010,1011,1100,1101,1110, while 1111 repeats the four-level state. "
                        + "Each round assigns mass 3/16 to each result and repeats with mass 1/16. "
                        + "The resulting law is uniform and its expected length is 18/5. "
                        + "Its stopping words use the public fixed-label carry-tree contract. "
                        + "ActualJointResponseCostCore.result supplies a recipe and cost domination "
                        + "for the selected controller. Scale38NestedCompensation.root_excess on the "
                        + "whole prototype family gives a coordinate costing at least 22 on every tape. "
                        + "Repeating that coordinate in all N slots and dropping the nonnegative bit "
                        + "charge gives the H lower bound. Scale36ActualEndpointAcquisition.result "
                        + "supplies a coarse endpoint costing at most 22 on each prototype; its "
                        + "point sampler pays zero bits and attains the H value.")),
                        Paragraph(Text("The dyadic random-bit cost is classical Knuth-Yao theory, "
                        + "as recalled in Lumbroso, Section 2.1. The complete tree-controller "
                        + "optimization and its raw and coarse batch comparison are repository results."))),
                    DescribeRole.Theorem))));
    }
}
