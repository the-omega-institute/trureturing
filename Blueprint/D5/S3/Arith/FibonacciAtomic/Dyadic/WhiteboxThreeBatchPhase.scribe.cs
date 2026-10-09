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
        var b = V("biasedThree"); var u = V("uniformThree"); var d = V("d"); var i = V("i");
        var w = V("w"); var t = V("t"); var point = V("point");
        Formula Stops(Formula path, int depth) => Call("stopping", D(3), path, Digits(depth));
        Formula Continue(Formula path) => Call("continuing", D(3), path, D(2));
        var bs = Call("relabel", V("rotate"), Call("fromPath", D(3), b));
        var us = Call("fromPath", D(3), u);
        return And(
            All(d, Nat, All(w, Seq(Call("Fin", d), Sp, To, Sp, V("Bool")),
                Equal(Call("observe", point, d, w), Call("some", D(0))))),
            Equal(Call("bill", point), Par(Seq(t, Colon, Sp, V("Tape"), Sp, Mapsto, Sp, D(0)))),
            Equal(Call("rotateLabels", Stops(b, 0), V("rotate")), Words(("0", 0))),
            Equal(Call("rotateLabels", Stops(b, 1), V("rotate")), Words(("10", 1), ("11", 2))),
            Equal(Continue(b), Seq(OpenBracket, CloseBracket)),
            Equal(Stops(u, 1), Words(("00", 0), ("01", 1), ("10", 2))),
            Equal(Continue(u), Call("list", Word("11"))),
            All(d, Nat, And(
                Equal(Call("state", u, Seq(d, Sp, Plus, Sp, D(2))), Call("state", u, d)),
                Equal(Call("action", u, Seq(d, Sp, Plus, Sp, D(2))), Call("action", u, d)))),
            All(i, Call("Fin", D(3)), Equal(Call("law", bs, i),
                Call("if", Equal(i, D(0)), Frac(D(1), 2), Frac(D(1), 4)))),
            All(i, Call("Fin", D(3)), Equal(Call("law", us, i), Frac(D(1), 3))),
            Equal(Call("E", Call("bill", bs)), Call("ofReal", Frac(D(3), 2))),
            Equal(Call("E", Call("bill", us)), Call("ofReal", Frac(D(8), 3))));
    }

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(And(Call("CodeClaim"), statement))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula RecipeRestriction()
    {
        var m = V("m"); var f = V("F"); var a = V("S"); var t = V("T");
        var r = V("r"); var q = V("q"); var i = V("i"); var fin = Call("Fin", m);
        return All(m, Nat, All(f, Seq(fin, Sp, To, Sp, V("Source")),
            All(a, Call("Finset", fin), All(r, Call("Recipe", f, a),
                All(t, Call("Finset", fin), Imp(Call("Subset", t, a),
                    Imp(Call("Nonempty", t), Ex(q, Call("Recipe", f, t),
                        All(i, fin, Imp(Call("Member", i, t),
                            Seq(Call("gain", q, i), Sp, Le, Sp, Call("gain", r, i))))))))))));
    }
    private static Formula ZeroGainUnique()
    {
        var m = V("m"); var f = V("F"); var a = V("S"); var r = V("r");
        var i = V("i"); var j = V("j"); var fin = Call("Fin", m);
        return All(m, Nat, All(f, Seq(fin, Sp, To, Sp, V("Source")),
            Imp(All(i, fin, All(j, fin, Call("Nonconflict", Call("F", i), Call("F", j)))),
                All(a, Call("Finset", fin), All(r, Call("Recipe", f, a),
                    All(i, fin, All(j, fin, Imp(And(Call("Member", i, a), Call("Member", j, a),
                        Equal(Call("gain", r, i), D(0)), Equal(Call("gain", r, j), D(0))),
                        Equal(i, j)))))))));
    }
    private static Formula SelectedEmission()
    {
        var s = V("s"); var t = V("t"); var p = V("p");
        return All(s, Call("PrefixSampler", V("Strategy")), All(t, V("Tape"),
            All(p, V("Strategy"), Imp(Call("Member", t, Call("emitted", s, p)),
                Equal(Call("selected", s, t), p)))));
    }

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
                new DocumentBlock.DisplayFormula(All(n, Nat, All(l, Real,
                    Equal(sharp, Call("min", first, Call("min", middle, last)))))),
                Helper("restrict_recipe", "Restricting a recipe does not increase excess", RecipeRestriction(),
                    "Removing evaluated trees preserves a recipe for every nonempty subfamily with no larger individual excess. "
                    + "At a node that stops separating the restricted family, the common child replaces that node."),
                Helper("zero_gain_unique", "There is at most one zero-excess member", ZeroGainUnique(),
                    "Restricting to two zero-excess trees would contradict the root excess bound for a nonconflicting family."),
                Helper("selected_emitted", "The selected controller is the emitted controller", SelectedEmission(),
                    "Persistence makes distinct controller emission events disjoint, so selection agrees with every emitted controller."),
                Describe.Lean(DescribeId.Create("code-claim"), DeclarationHandle.Create(Prefix + "CodeClaim"),
                    H("Literal attaining codes"),
                    StatementSource.FromAuthor(Disp(Equal(Call("CodeClaim"), CodesFormula()))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Stopping at depth d returns words of length d+1. "
                        + "The biased sampler rotates carry labels by one modulo three: its words "
                        + "0, 10, and 11 emit endpoint labels 0, 1, and 2. The point sampler "
                        + "emits label zero at the empty prefix and pays no bits. The uniform "
                        + "path repeats its state and action every two depths, continuing on 11. "
                        + "Expectations use the common fair-tape measure."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Exact values, thresholds, and attained infima"),
                    StatementSource.FromAuthor(Disp(And(Call("CodeClaim"), statement))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
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
                        + "pays zero bits. The words 0, 10, and 11 emit labels 0, 1, and 2, giving probabilities 1/2,1/4,1/4 "
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
