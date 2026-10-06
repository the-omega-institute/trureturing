using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class InitializedControlProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Persistent endpoint states, agreed public roots and sender-local bit queries generate actual support and protocol-realized transitions.",
        H("Initialized endpoint control protocols"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("endpoint-protocol"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/InitializedControlProtocol.EndpointProtocol"),
                H("A source-local public prefix protocol"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A public bit prefix determines either a tagged sender-local Boolean question or a leaf. A "
                        + "left question reads only the old left state and a right question reads only the old right "
                        + "state. Each leaf output takes only its own old local state and the transmitted Boolean "
                        + "string. Query labels are evaluator data reconstructed from the public prefix, and the leaf "
                        + "outputs never read them as an additional channel.")),
                    Paragraph(Math(TraceFormula())),
                    Paragraph(Text(
                        "All universe levels u,v,w,x are arbitrary. rightSender and leftSender test the "
                        + "right and left question tags of a trace entry. The evaluator is "
                        + "PassivePolicyNormalization.execute. Its input and the two local carriers "
                        + "are arbitrary types. Finite fuel is evidence of termination on the actual input; it is not a "
                        + "uniform tree depth or an endpoint runtime argument."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-controller"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/InitializedControlProtocol.Controller"),
                H("Initialized persistent endpoint compliance"),
                StatementSource.FromAuthor(ControllerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The original source is the direct product of the data vector and its control coordinate. The "
                        + "action alphabet includes every data basis translation, the control basis translation, and "
                        + "every established controlRewrite. A fixed complementary pair of submodules supplies the two "
                        + "original readouts.")),
                    Paragraph(Math(ActionsFormula())),
                    Paragraph(Text(
                        "Reachable is the least predicate containing all initial pairs and closed "
                        + "under successful commits; the formula gives its induction characterization. Each endpoint "
                        + "initializes from its own original projection and reads that projection back "
                        + "exactly. Operational reachability begins with the full local initialization product and "
                        + "closes under successful executions and the two local leaf commits. Both local carriers must "
                        + "be exactly projections of this operational support.")),
                    Paragraph(Text(
                        "Compliance requires locally selected roots to agree on actual support, finite termination "
                        + "there, both prescribed source readout equations after every execution, and zero-bit basis "
                        + "translations. Neither local carrier nor the root type is assumed finite. The readout "
                        + "equations specify correctness and do not implement a centralized transition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realized-controller-step"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/InitializedControlProtocol.step"),
                H("Actual support determines a total realized step"),
                StatementSource.FromAuthor(StepFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an actual reachable pair and a public action, finite termination selects a successful "
                        + "evaluator transcript. The successor consists of the two local leaf updates on its Boolean "
                        + "responses. Operational closure places it back in the actual reachable subtype. Step cost is "
                        + "the transcript length. Existing runWord and Comm supply word execution and cumulative cost."))),
                DescribeRole.Definition))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula body) => Seq(Open, body, Close);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula A(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.Add(Land);
            items.Add(P(clause));
        }
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, P(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, type, Comma, P(body));
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(P(premise), Implies, Sp, P(body));
    private static Formula E(Formula left, Formula right) => Seq(left, Eq, right);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, right, Close);
    private static Formula Arr(Formula left, Formula right) => Seq(P(left), To, Sp, P(right));
    private static Formula Ty(string level) => Seq(V("Type"), Underscore, Grp(V(level)));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Bit => C("ZMod", D(2));
    private static Formula Bool => C("Bool");
    private static Formula List(Formula type) => C("List", type);

    private static Formula EndpointFormula()
    {
        Formula ma = V("MA"), mb = V("MB"), oa = V("OA"), ob = V("OB");
        Formula fields = Seq(OpenBrace,
            V("node"), Colon, Arr(List(Bool), C("Sum", C("Question", ma, mb), C("Unit"))), Comma,
            V("outA"), Colon, Arr(ma, Arr(List(Bool), oa)), Comma,
            V("outB"), Colon, Arr(mb, Arr(List(Bool), ob)), CloseBrace);
        return Disp(All("MA", Ty("u"), All("MB", Ty("v"),
            All("OA", Ty("w"), All("OB", Ty("x"), A(
                E(C("Question", ma, mb), C("Sum", Arr(ma, Bool), Arr(mb, Bool))),
                E(C("EndpointProtocol", ma, mb, oa, ob), fields)))))));
    }

    private static Formula ControllerFormula()
    {
        Formula d = V("d"), a = V("A"), b = V("B"), h = V("h"), c = V("C");
        Formula ma = V("MA"), mb = V("MB"), rt = V("Root"), m = V("m"), f = V("f");
        Formula t = V("t"), x = V("a"), y = V("b");
        Formula source = C("Source", d), actions = C("Action", d);
        Formula trace = C("Trace", ma, mb), product = C("Prod", ma, mb);
        Formula reach = C("Reachable", c, m), exec = C("Exec", c, f, m, t);
        Formula init = Pair(C("initA", c, x), C("initB", c, y));
        Formula z = Seq(C("readA", c, C("fst", m)), Plus, C("readB", c, C("snd", m)));
        Formula commit = C("commit", c, f, m, t);
        Formula p = C("protocol", c, f, C("rootA", c, f, C("fst", m)));
        Formula dataFields = Seq(OpenBrace,
            V("readA"), Colon, Arr(ma, a), Comma, V("readB"), Colon, Arr(mb, b), Comma,
            V("initA"), Colon, Arr(a, ma), Comma, V("initB"), Colon, Arr(b, mb), Comma,
            V("readInitA"), Colon, All("a", a, E(C("readA", C("initA", x)), x)), Comma,
            V("readInitB"), Colon, All("b", b, E(C("readB", C("initB", y)), y)), Comma,
            V("rootA"), Colon, Arr(actions, Arr(ma, rt)), Comma,
            V("rootB"), Colon, Arr(actions, Arr(mb, rt)), Comma,
            V("protocol"), Colon, Arr(actions, Arr(rt, C("EndpointProtocol", ma, mb, ma, mb))),
            CloseBrace);
        Formula r = V("R"), m0 = V("mzero");
        Formula generators = A(
            All("a", a, All("b", b, C("apply", r, init))),
            All("mzero", product, Imp(C("apply", r, m0), All("f", actions, All("t", trace,
                Imp(C("Exec", c, f, m0, t), C("apply", r, C("commit", c, f, m0, t))))))));
        Formula operations = A(
            Seq(C("Exec", c, f, m, t), Iff, Sp, P(Ex("n", N,
                E(C("execute", C("answer"), C("policy", p), V("n"), C("nil"), m),
                    C("some", Pair(t, C("unit"))))))),
            E(commit, Pair(C("outA", p, C("fst", m), C("bits", t)),
                C("outB", p, C("snd", m), C("bits", t)))),
            Seq(C("Reachable", c, m), Iff, Sp, P(All("R", Arr(product, C("Prop")), Imp(generators, C("apply", r, m))))));
        Formula laws = A(
            All("m", product, Imp(reach, All("f", actions,
                E(C("rootA", c, f, C("fst", m)), C("rootB", c, f, C("snd", m)))))),
            All("m", product, Imp(reach, All("f", actions, Ex("t", trace, exec)))),
            All("x", ma, Ex("y", mb, C("Reachable", c, Pair(V("x"), V("y"))))),
            All("y", mb, Ex("x", ma, C("Reachable", c, Pair(V("x"), V("y"))))),
            All("m", product, Imp(reach, All("f", actions, All("t", trace,
                Imp(exec, A(
                    E(C("readA", c, C("fst", commit)), C("pA", C("apply", f, z))),
                    E(C("readB", c, C("snd", commit)), C("pB", C("apply", f, z))))))))),
            All("m", product, Imp(reach, All("t", trace, A(
                All("i", C("Fin", d), Imp(C("Exec", c, C("dataTranslation", V("i")), m, t),
                    E(t, C("nil")))),
                Imp(C("Exec", c, C("controlTranslation"), m, t), E(t, C("nil"))))))));
        Formula content = A(
            E(source, C("Prod", Arr(C("Fin", d), Bit), Bit)),
            E(C("pA"), C("projectionOnto", a, b, h)),
            E(C("pB"), C("projectionOnto", b, a, C("symm", h))),
            E(C("ControllerData", d, a, b, ma, mb, rt), dataFields),
            All("C", C("ControllerData", d, a, b, ma, mb, rt),
                All("f", actions, All("m", product, All("t", trace, operations)))),
            E(C("Controller", h, ma, mb, rt), Seq(OpenBrace,
                c, Colon, C("ControllerData", d, a, b, ma, mb, rt), Mid, Sp, laws, CloseBrace)));
        return Disp(All("d", N, All("A", C("Submodule", Bit, source),
            All("B", C("Submodule", Bit, source), All("h", C("IsCompl", a, b),
            All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"), content))))))));
    }

    private static Formula StepFormula()
    {
        Formula c = V("C"), f = V("f"), m = V("m"), t = V("t"), h = V("h");
        Formula ma = V("MA"), mb = V("MB"), root = V("Root");
        Formula product = C("Prod", ma, mb), data = C("toControllerData", c);
        Formula actual = Seq(OpenBrace, V("q"), Colon, product, Mid, Sp, C("Reachable", data, V("q")), CloseBrace);
        Formula chosen = C("choose", Ex("t", C("Trace", ma, mb),
            C("Exec", data, f, C("val", m), t)));
        Formula formulas = A(
            E(C("State", c), actual),
            E(C("trace", c, f, m), chosen),
            E(C("val", C("step", c, f, m)),
                C("commit", data, f, C("val", m), C("trace", c, f, m))),
            E(C("cost", c, m, f), C("length", C("trace", c, f, m))),
            E(C("val", C("initial", c, V("a"), V("b"))),
                Pair(C("initA", c, V("a")), C("initB", c, V("b")))),
            E(C("readout", c, m), Seq(C("readA", c, C("fst", C("val", m))), Plus,
                C("readB", c, C("snd", C("val", m))))));
        return Disp(All("d", N, All("A", C("Submodule", Bit, C("Source", V("d"))),
            All("B", C("Submodule", Bit, C("Source", V("d"))),
            All("h", C("IsCompl", V("A"), V("B")),
            All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"),
            All("C", C("Controller", h, ma, mb, root),
            All("a", V("A"), All("b", V("B"), All("f", C("Action", V("d")),
            All("m", C("State", c), formulas)))))))))))));
    }


    private static Formula TraceFormula()
    {
        Formula ma = V("MA"), mb = V("MB"), p = V("p"), t = V("t"), prefix = V("h");
        Formula q = C("Question", ma, mb), hist = C("Trace", ma, mb);
        Formula question = V("q"), answer = V("y"), tail = V("tail"), pair = Pair(V("a"), V("b"));
        Formula equations = A(
            E(hist, List(C("Sigma", Seq(question, Colon, q, Mapsto, Sp, Bool)))),
            All("t", hist, E(C("bits", t), C("map", Seq(V("e"), Mapsto, Sp, C("snd", V("e"))), t))),
            All("left", Arr(ma, Bool), All("a", ma, All("b", mb,
                E(C("answer", C("inl", V("left")), pair), C("apply", V("left"), V("a")))))),
            All("right", Arr(mb, Bool), All("a", ma, All("b", mb,
                E(C("answer", C("inr", V("right")), pair), C("apply", V("right"), V("b")))))),
            All("t", hist, A(
                E(C("policy", p, t), C("node", p, C("bits", t))),
                E(C("rightCount", t), C("length", C("filter", C("rightSender"), t))),
                E(C("leftCount", t), C("length", C("filter", C("leftSender"), t))))),
            All("h", List(Bool), A(
                Seq(C("PublicTrace", p, prefix, C("nil")), Iff, Sp, P(E(C("node", p, prefix), C("inr", C("unit"))))),
                All("q", q, All("y", Bool, All("tail", hist,
                    Seq(C("PublicTrace", p, prefix, C("cons", Pair(question, answer), tail)), Iff, Sp, P(A(E(C("node", p, prefix), C("inl", question)),
                            C("PublicTrace", p, C("append", prefix, C("singleton", answer)), tail))))))))));
        return Disp(All("MA", Ty("u"), All("MB", Ty("v"), All("OA", Ty("w"), All("OB", Ty("x"),
            All("p", C("EndpointProtocol", ma, mb, V("OA"), V("OB")), equations))))));
    }
    private static Formula ActionsFormula()
    {
        Formula d = V("d"), i = V("i"), z = V("z");
        Formula source = C("Source", d), e = Pair(C("single", i, D(1)), D(0));
        Formula control = Pair(D(0), D(1));
        return Disp(All("d", N, A(
            E(source, C("Prod", Arr(C("Fin", d), Bit), Bit)),
            E(C("Action", d), Seq(
                OpenBrace, C("dataTranslation", i), Mid, Sp, i, InMacro, Sp, C("Fin", d), CloseBrace, Cup, Sp, OpenBrace, C("controlTranslation"), CloseBrace, Cup, Sp, OpenBrace, C("rewrite", i), Mid, Sp, i, InMacro, Sp, C("Fin", d), CloseBrace)),
            All("i", C("Fin", d), All("z", source, A(
                E(C("apply", C("dataTranslation", i), z), Seq(z, Plus, e)),
                E(C("apply", C("rewrite", i), z), C("controlRewrite", i, z)),
                E(C("controlRewrite", i, z), Pair(C("single", i, C("snd", z)), D(0)))))),
            All("z", source, E(C("apply", C("controlTranslation"), z), Seq(z, Plus, control))))));
    }
}
