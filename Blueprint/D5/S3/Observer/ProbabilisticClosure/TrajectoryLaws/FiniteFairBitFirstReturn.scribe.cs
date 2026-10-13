using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FiniteFairBitFirstReturnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FiniteFairBitFirstReturn", H("Sequential fair requests and invocation events"), Blocks(
            Paragraph(Text("A decoded instruction either performs one deterministic transition or requests one external fair bit. The execution reads the head of the unused iid stream only in the fair case. The stream and its consumed index are probability coordinates; neither is a persistent machine register. Coincident fair successors contribute both half masses to the same state.")),
            Paragraph(Text("The finite prefix proof inducts over physical instructions. A deterministic step keeps the entire unused stream. A fair step uses independence of its head and suffix, proved by the existing FreshServiceRestart first acceptance theorem with the full acceptance set. The two head values give disjoint cylinder events. Their masses add, including when their successors coincide. Only after this operational induction does MarkovPrefixMass identify the cylinders with Kernel.trajMeasure.")),
            ExactNode("split_tape"),
            ExactNode("unused_suffix"),
            ExactNode("measurable_run"),
            ExactNode("row_fair"),
            ExactNode("charged_cardinality"),
            Node("prefix", "execution_prefix_law", "Operational finite prefix law", PrefixStatement()),
            Paragraph(Text("The local command syntax contains bit reads and branches, writes, bounded head moves, fair branches, fair bit stores, single symbol buffers, renderer sends, semantic letter emissions and returns. Mode and supplied input are explicit snapshot fields. Arbitrary finite work, persistent phases and computing provider state must occupy charged tape cells. Launch installs its specified entry and input; it does not inspect a previous return. An absent entry gives immediate completion and preserves the remaining snapshot fields.")),
            Paragraph(Text("Return and semantic emission are primitive events, distinct from renderer characters. A semantic letter can be emitted before its bit is erased. The event cut is a coordinate on this same execution, and the bounded executor continues until its first return. It preserves the entire returned snapshot. It introduces no saved semantic letter, accumulated output log or runtime reset.")),
            Node("return", "invocation_return_iff", "First return and bounded execution", ReturnStatement()),
            Paragraph(Text("A complete codec represents the fixed installed program and each admitted micro snapshot in one fixed width binary word. Its round trip is an original representation premise. The micro carrier is the common primitive reachability closure of all supplied entrance snapshots. Induction on physical steps proves that every run from this closure stays in it. The codec yields injectivity and bounds this actual carrier and its ready subset by the number of binary words. The same execution satisfies the request count suffix identity and the physical finite prefix law.")),
            Node("charged", "charged_execution_prefix", "Charged primitive execution", ChargedStatement()),
            Paragraph(Text("The complete codec premise does not prove an implementation of compressed instruction fetching, field decoding or installation temporaries at a given peak. Applying this calculus to the entire charged digital source class still requires a refinement of those paid routines and the original native field layout, preserving primitive events and lawful entrance addresses. Head movement in the local calculus holds at a boundary; applying it to an original program also requires its valid movement boundary. No source prior sampler or receiver archive is encoded by this calculus. Almost sure returns, normalized exit probabilities, reachable state escape, native law correspondence and denominator bounds are separate mathematical obligations.")))));

    private static DocumentBlock.Describe ExactNode(string name) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This existing source lemma is reused directly by the operational certificate."))),
            DescribeRole.Theorem);

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The Lean proof establishes exactly this statement under its displayed premises."))),
            DescribeRole.Theorem);

    private static Formula PrefixStatement()
    {
        var s = N("S"); var d = N("decode"); var z = N("s"); var n = N("n"); var w = N("w");
        return Seq(All("S", N("Type")), Instances(s), All("decode", Arrow(s, App("Instruction", s))),
            All("s", s), All("n", Nat), All("w", Arrow(FinPlus(n), s)),
            Mass(N("tapeLaw"), Lambda("omega", Lambda("i", FinPlus(n), App("run", d, z, N("omega"), App("val", N("i"))))), w),
            Sp, Eq, Sp, KernelMass(d, z, n, w));
    }

    private static Formula ReturnStatement()
    {
        var p = N("p"); var m = N("m"); var a = N("a"); var prog = N("P");
        var start = App("launch", prog, N("s"), N("mode"), N("input")); var omega = N("omega"); var n = N("n"); var t = N("t"); var k = N("k");
        return Seq(All("p", Nat), All("m", Nat), All("a", Nat), All("P", App("Program", p, a)),
            All("s", App("Snapshot", p, m, a)), All("mode", N("ServiceMode")),
            All("input", App("Option", N("Letter"))), All("omega", Arrow(Nat, N("Bool"))),
            All("n", Nat), All("t", App("Snapshot", p, m, a)),
            App("executeUntil", prog, start, omega, n), Sp, Eq, Sp, App("some", t), Sp, Iff, Sp,
            Exists, Sp, k, Sp, Le, Sp, n, Sp, Comma, Sp,
            App("firstReturnAt", prog, start, omega, k), Sp, Land, Sp,
            App("snapshot", App("fst", App("trace", prog, start, omega, k))), Sp, Eq, Sp, t);
    }

    private static Formula ChargedStatement()
    {
        var p = N("p"); var m = N("m"); var a = N("a"); var b = N("B"); var prog = N("P");
        var entrances = N("entrances"); var ready = N("ready"); var state = App("Snapshot", p, m, a);
        var micro = App("Set.setOf", Lambda("t", state, App("Reachable", prog, entrances, N("t"))));
        var z = N("s"); var n = N("n"); var w = N("w"); var d = App("decoded", prog);
        var omega = N("omega"); var k = N("k"); var v = N("z"); var bit = N("b");
        return Seq(All("p", Nat), All("m", Nat), All("a", Nat), All("B", Nat),
            All("P", App("Program", p, a)), All("entrances", App("Set", state)),
            App("CompleteCodec", prog, micro, b), Sp, To, Sp, All("ready", App("Set", micro)), SnapshotInstances(state),
            All("s", state), App("Reachable", prog, entrances, z), Sp, To, Sp,
            All("n", Nat), All("w", Arrow(FinPlus(n), state)),
            App("Nat.card", micro), Sp, Le, Sp, Pow(D(2), b), Sp, Land, Sp,
            App("Nat.card", ready), Sp, Le, Sp, Pow(D(2), b), Sp, Land, Sp,
            Open, All("omega", Arrow(Nat, N("Bool"))),
            App("Reachable", prog, entrances, App("physicalRun", prog, z, omega, n)), Close, Sp, Land, Sp,
            Open, All("z", state), All("b", N("Bool")), App("asks", App("code", prog, App("pc", v))),
            Sp, Eq, Sp, N("false"), Sp, To, Sp, App("act", prog, v, bit), Sp, Eq, Sp,
            App("act", prog, v, N("false")), Close, Sp, Land, Sp,
            Open, All("omega", Arrow(Nat, N("Bool"))), All("k", Nat),
            App("unused", d, z, omega, n, k), Sp, Eq, Sp,
            App("omega", Seq(k, Sp, Plus, Sp, App("requests", d, z, omega, n))), Close, Sp, Land, Sp,
            Mass(N("tapeLaw"), Lambda("omega", Lambda("i", FinPlus(n), App("physicalRun", prog, z, omega, App("val", N("i"))))), w),
            Sp, Eq, Sp, KernelMass(d, z, n, w));
    }

    private static Formula Instances(Formula s) => Seq(
        OpenBracket, App("Countable", s), CloseBracket, Sp,
        OpenBracket, App("MeasurableSpace", s), CloseBracket, Sp,
        OpenBracket, App("MeasurableSingletonClass", s), CloseBracket, Sp);
    private static Formula SnapshotInstances(Formula s) => Seq(
        OpenBracket, App("MeasurableSpace", s), CloseBracket, Sp,
        OpenBracket, App("MeasurableSingletonClass", s), CloseBracket, Sp);
    private static Formula KernelMass(Formula d, Formula s, Formula n, Formula w) =>
        Mass(App("instructionLaw", d, s), Lambda("x", Lambda("i", FinPlus(n), App("x", App("val", N("i"))))), w);
    private static Formula Mass(Formula law, Formula f, Formula w) =>
        Seq(App("Measure.map", f, law), Sp, OpenBrace, w, CloseBrace);
    private static Formula FinPlus(Formula n) => App("Fin", Seq(n, Sp, Plus, Sp, D(1)));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Sp, Comma, Sp);
    private static Formula Lambda(string name, Formula body) => Seq(N("fun"), Sp, N(name), Sp, Mapsto, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(N("fun"), Sp, Open, N(name), Sp, Colon, Sp, type, Close, Sp, Mapsto, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula App(string name, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Sp, Comma, Sp));
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return F.Seq(terms.ToArray());
    }
    private static Formula N(string name)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        var parts = name.Split('.');
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) terms.Add(Dot);
            terms.Add(Seq(Operatorname, Grp(F.Id(parts[i]))));
        }
        return F.Seq(terms.ToArray());
    }
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}
