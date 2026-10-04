using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlRewriteDirectionalBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every correct endpoint-local rewrite pays the required directions on each actual execution, and a fixed exchange attains both bounds.",
        H("Control rewrite directional communication"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("initialized-rewrite-correctness"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.RewriteCorrect"),
                H("Both original rewrite outputs after local preparation"),
                StatementSource.FromAuthor(CorrectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The original summary types are modules over ZMod 2, with control restrictions ellA and ellB "
                        + "and prescribed projection columns alpha and beta. Preparation maps them into arbitrary "
                        + "persistent local types. Correctness requires finite termination on every prepared pair and "
                        + "local outputs equal to (ellA(a)+ellB(b)) times their respective prescribed column."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-rewrite-exchange"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewriteProtocol"),
                H("The exact zero, one or two bit exchange"),
                StatementSource.FromAuthor(ExchangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The right endpoint sends its old control contribution precisely when alpha is nonzero and "
                        + "ellB is nonzero. The left endpoint sends its old contribution precisely when beta is nonzero "
                        + "and ellA is nonzero. The public order is right then left. A zero column produces zero "
                        + "locally; a zero remote restriction supplies a zero contribution locally. Both old summaries "
                        + "remain available until the leaf outputs commit. In the formulas get(h,j) is the optional "
                        + "list entry, and getD supplies false when it is absent; if(condition,x,y) is x when "
                        + "the condition holds and y otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rewrite-directional-sharpness"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewrite_directional_sharpness"),
                H("Sharp directions on every execution"),
                StatementSource.FromAuthor(SharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every successful evaluator history has the publicly determined query label at each preceding "
                        + "Boolean prefix and ends at its public leaf. Successful executions on one input are "
                        + "independent of sufficient fuel. These clauses apply to arbitrary persistent endpoint types.")),
                    Paragraph(Text(
                        "For every correct protocol and every prepared original input, right-to-left bit count is at "
                        + "least the indicator of alpha nonzero and ellB nonzero, and left-to-right count is at least "
                        + "the indicator of beta nonzero and ellA nonzero. Both bounds concern the same execution. "
                        + "Their sum is a lower bound on its total bit length.")),
                    Paragraph(Text(
                        "If the right-to-left count were zero, fixing the left prepared state and changing the right "
                        + "original summary by a control-one vector preserves the entire finite path. All questions on "
                        + "that path read only the unchanged left state, so the same public leaf and left output "
                        + "contradict the prescribed nonzero change. The symmetric argument proves the other direction.")),
                    Paragraph(Text(
                        "The fixed exchange is correct on every original input and attains both direction counts and "
                        + "their sum. Its successful witnesses use at most three units of evaluator fuel, including the "
                        + "public leaf. The lower bound permits arbitrary public trees with finite actual termination "
                        + "and imposes no global depth."))),
                DescribeRole.Theorem))));

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
    private static Formula NE(Formula left, Formula right) => Seq(left, Neq, Sp, right);
    private static Formula LE(Formula left, Formula right) => Seq(left, Le, Sp, right);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, right, Close);
    private static Formula Arr(Formula left, Formula right) => Seq(P(left), To, Sp, P(right));
    private static Formula Ty(string level) => Seq(V("Type"), Underscore, Grp(V(level)));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Bit => C("ZMod", D(2));
    private static Formula Bool => C("Bool");
    private static Formula List(Formula type) => C("List", type);

    private static Formula PreparedExecution(Formula p, Formula a, Formula b, Formula n, Formula t)
        => E(C("execute", C("answer"), C("policy", p), n, C("nil"), Pair(a, b)),
            C("some", Pair(t, C("unit"))));

    private static Formula CorrectFormula()
    {
        Formula a = V("A"), b = V("B"), ma = V("MA"), mb = V("MB"), p = V("p");
        Formula ea = V("ellA"), eb = V("ellB"), alpha = V("alpha"), beta = V("beta");
        Formula ia = V("initA"), ib = V("initB"), x = V("a"), y = V("b"), t = V("t");
        Formula exec = PreparedExecution(p, C("apply", ia, x), C("apply", ib, y), V("n"), t);
        Formula scalar = Seq(C("apply", ea, x), Plus, C("apply", eb, y));
        Formula body = A(
            All("a", a, All("b", b, Ex("n", N, Ex("t", C("Trace", ma, mb), exec)))),
            All("a", a, All("b", b, All("n", N, All("t", C("Trace", ma, mb),
                Imp(exec, A(
                    E(C("outA", p, C("apply", ia, x), C("bits", t)), C("smul", scalar, alpha)),
                    E(C("outB", p, C("apply", ib, y), C("bits", t)), C("smul", scalar, beta)))))))));
        return Disp(All("A", Ty("u"), All("B", Ty("v"),
            Imp(A(C("AddCommGroup", a), C("Module", Bit, a),
                C("AddCommGroup", b), C("Module", Bit, b)),
            All("MA", Ty("w"), All("MB", Ty("x"),
            All("ellA", C("LinearMap", Bit, a, Bit),
            All("ellB", C("LinearMap", Bit, b, Bit), All("alpha", a, All("beta", b,
            All("initA", Arr(a, ma), All("initB", Arr(b, mb),
            All("p", C("EndpointProtocol", ma, mb, a, b),
                Seq(C("RewriteCorrect", ea, eb, alpha, beta, ia, ib, p), Iff, Sp, P(body)))))))))))))));
    }

    private static Formula ExchangeFormula()
    {
        Formula a = V("A"), b = V("B"), ea = V("ellA"), eb = V("ellB");
        Formula alpha = V("alpha"), beta = V("beta"), h = V("h"), p = V("p");
        Formula needR = A(NE(alpha, D(0)), NE(eb, D(0)));
        Formula needL = A(NE(beta, D(0)), NE(ea, D(0)));
        Formula bitValue(Formula j) => C("if", C("getD", C("get", h, j), C("false")), D(1), D(0));
        Formula r = C("if", needR, D(1), D(0));
        Formula node = C("if", A(needR, E(C("length", h), D(0))),
            C("inl", C("inr", Seq(V("b"), Mapsto, Sp, C("decide", E(C("apply", eb, V("b")), D(1)))))),
            C("if", A(needL, E(C("length", h), r)),
                C("inl", C("inl", Seq(V("a"), Mapsto, Sp, C("decide", E(C("apply", ea, V("a")), D(1)))))),
                C("inr", C("unit"))));
        Formula outputA = C("if", E(alpha, D(0)), D(0),
            C("smul", Seq(C("apply", ea, V("a")), Plus,
                C("if", E(eb, D(0)), D(0), bitValue(D(0)))), alpha));
        Formula outputB = C("if", E(beta, D(0)), D(0),
            C("smul", Seq(C("apply", eb, V("b")), Plus,
                C("if", E(ea, D(0)), D(0), bitValue(r))), beta));
        Formula body = A(
            E(C("directionDemand", alpha, eb), r),
            E(C("directionDemand", beta, ea), C("if", needL, D(1), D(0))),
            E(C("rewriteCost", ea, eb, alpha, beta),
                Seq(C("directionDemand", alpha, eb), Plus, C("directionDemand", beta, ea))),
            E(p, C("rewriteProtocol", ea, eb, alpha, beta)),
            All("h", List(Bool), E(C("node", p, h), node)),
            All("a", a, All("h", List(Bool), E(C("outA", p, V("a"), h), outputA))),
            All("b", b, All("h", List(Bool), E(C("outB", p, V("b"), h), outputB))));
        return Disp(All("A", Ty("u"), All("B", Ty("v"),
            Imp(A(C("AddCommGroup", a), C("Module", Bit, a),
                C("AddCommGroup", b), C("Module", Bit, b)),
            All("ellA", C("LinearMap", Bit, a, Bit),
            All("ellB", C("LinearMap", Bit, b, Bit), All("alpha", a, All("beta", b,
            All("p", C("EndpointProtocol", a, b, a, b),
                Imp(E(p, C("rewriteProtocol", ea, eb, alpha, beta)), body))))))))));
    }

    private static Formula SharpnessFormula()
    {
        Formula a = V("A"), b = V("B"), ea = V("ellA"), eb = V("ellB");
        Formula alpha = V("alpha"), beta = V("beta"), ma = V("MA"), mb = V("MB"), p = V("p");
        Formula x = V("a"), y = V("b"), n = V("n"), t = V("t"), s = V("s");
        Formula ep = C("EndpointProtocol", ma, mb, a, b), tr = C("Trace", ma, mb);
        Formula demandR = C("directionDemand", alpha, eb), demandL = C("directionDemand", beta, ea);
        Formula cost = C("rewriteCost", ea, eb, alpha, beta);
        Formula exec = PreparedExecution(p, x, y, n, t);
        Formula labels = All("MA", Ty("w"), All("MB", Ty("x"), All("p", ep,
            All("a", ma, All("b", mb, All("n", N, All("t", tr,
                Imp(exec, C("PublicTrace", p, C("nil"), t)))))))));
        Formula uniqueness = All("MA", Ty("w"), All("MB", Ty("x"), All("p", ep,
            All("a", ma, All("b", mb, All("n", N, All("m", N,
            All("t", tr, All("s", tr, Imp(A(exec,
                PreparedExecution(p, x, y, V("m"), s)), E(t, s)))))))))));
        Formula lower = All("MA", Ty("w"), All("MB", Ty("x"),
            All("initA", Arr(a, ma), All("initB", Arr(b, mb), All("p", ep,
            Imp(C("RewriteCorrect", ea, eb, alpha, beta, V("initA"), V("initB"), p),
            All("a", a, All("b", b, All("n", N, All("t", tr,
                Imp(PreparedExecution(p, C("apply", V("initA"), x),
                    C("apply", V("initB"), y), n, t),
                    A(LE(demandR, C("rightCount", t)), LE(demandL, C("leftCount", t)),
                        LE(cost, C("length", t))))))))))))));
        Formula fixedP = C("rewriteProtocol", ea, eb, alpha, beta);
        Formula attained = All("a", a, All("b", b, Ex("n", N, Ex("t", C("Trace", a, b),
            A(PreparedExecution(fixedP, x, y, n, t), E(C("rightCount", t), demandR),
                E(C("leftCount", t), demandL), E(C("length", t), cost))))));
        Formula body = A(labels, uniqueness, lower,
            C("RewriteCorrect", ea, eb, alpha, beta, C("id"), C("id"), fixedP), attained);
        return Disp(All("A", Ty("u"), All("B", Ty("v"),
            Imp(A(C("AddCommGroup", a), C("Module", Bit, a),
                C("AddCommGroup", b), C("Module", Bit, b)),
            All("ellA", C("LinearMap", Bit, a, Bit), All("ellB", C("LinearMap", Bit, b, Bit),
            All("alpha", a, All("beta", b, body))))))));
    }

}
