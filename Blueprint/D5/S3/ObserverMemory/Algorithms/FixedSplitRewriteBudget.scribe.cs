using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedSplitRewriteBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same noncentral direct sum has sharp worst initial rewrite cost one or two, and every persistent cumulative controller obeys that lower bound.",
        H("Sharp rewrite budget for a fixed split"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-split-cost"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.splitCost"),
                H("Cost of an original data rewrite"),
                StatementSource.FromAuthor(CostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Keep the original direct sum and its projections fixed. The data basis column on each side "
                        + "and the opposite control restriction determine the two required direction indicators. Their "
                        + "sum is the exact initial rewrite cost. Cstar is the finite supremum over all original data "
                        + "columns."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-cumulative-budget"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.UniformCumulativeBudget"),
                H("One bound for all initialized action words"),
                StatementSource.FromAuthor(UniformFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A uniform cumulative budget quantifies every original local summary pair and every finite "
                        + "word in the complete original action alphabet. Costs use Comm on the actual operational "
                        + "state subtype and its protocol-realized step and bit-length cost."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-split-rewrite-budget"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.fixed_split_rewrite_budget"),
                H("Classification and necessary persistent budget"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every data dimension at least two and every fixed complementary pair of original "
                        + "submodules of positive dimensions, Cstar is one if either control restriction is zero and "
                        + "two if both restrictions are nonzero. There is at least one rewrite of positive cost. Cstar "
                        + "is the least uniform budget for correct initial rewrite protocols on all original summary "
                        + "pairs.")),
                    Paragraph(Text(
                        "For any compliant persistent controller with arbitrary local and root types, every initial "
                        + "rewrite execution pays both directional indicators, and every uniform cumulative budget K "
                        + "satisfies Cstar at most K. Full local-product initialization makes each action root "
                        + "constant; composing the local leaf updates with their fixed readouts gives a prepared-input "
                        + "rewrite protocol without transporting or exposing query labels.")),
                    Paragraph(Text(
                        "The classification uses the same fixed projections. With control on one side, a nonzero "
                        + "vector in the opposite summand lies in data space, so some projected data column is nonzero. "
                        + "With both restrictions nonzero, choose control-one vectors in both summands. Their sum lies "
                        + "in data space. If every left projected data column had zero control, linearity would "
                        + "contradict the chosen left control-one vector. A column with nonzero left control also has a "
                        + "nonzero right projection because its total control is zero.")),
                    Paragraph(Text(
                        "This statement supplies the initial-rewrite budget lower bound and the classification "
                        + "required by the persistent theorem. It does not assert the restricted persistent-state "
                        + "construction, saturated silent successors, memory lower embeddings, exact all-word first- "
                        + "rewrite costs, storage minima, or completion of the full original theorem."))),
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
    private static Formula LT(Formula left, Formula right) => Seq(left, Lt, right);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, right, Close);
    private static Formula Ty(string level) => Seq(V("Type"), Underscore, Grp(V(level)));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Bit => C("ZMod", D(2));
    private static Formula List(Formula type) => C("List", type);

    private static Formula SplitContext(Formula body)
    {
        Formula d = V("d"), a = V("A"), b = V("B");
        return All("d", N, All("A", C("Submodule", Bit, C("Source", d)),
            All("B", C("Submodule", Bit, C("Source", d)),
            All("h", C("IsCompl", a, b), body))));
    }
    private static Formula CostFormula()
    {
        Formula h = V("h"), i = V("i"), a = V("A"), b = V("B");
        Formula e = Pair(C("single", i, D(1)), D(0));
        Formula alpha = C("pA", e), beta = C("pB", e), ea = C("ell", a), eb = C("ell", b);
        Formula correct = C("RewriteCorrect", ea, eb, alpha, beta, C("id"), C("id"), V("p"));
        Formula exec = E(C("execute", C("answer"), C("policy", V("p")), V("n"),
            C("nil"), Pair(V("a"), V("b"))), C("some", Pair(V("t"), C("unit"))));
        Formula initialBudget = All("i", C("Fin", V("d")),
            Ex("p", C("EndpointProtocol", a, b, a, b), A(correct,
                All("a", a, All("b", b, All("n", N, All("t", C("Trace", a, b),
                    Imp(exec, LE(C("length", V("t")), V("K"))))))))));
        return Disp(SplitContext(A(
            E(C("pA"), C("projectionOnto", a, b, h)),
            E(C("pB"), C("projectionOnto", b, a, C("symm", h))),
            All("S", C("Submodule", Bit, C("Source", V("d"))),
                E(C("ell", V("S")), C("compose", C("sndLinearMap"), C("subtype", V("S"))))),
            All("i", C("Fin", V("d")),
                E(C("splitCost", h, i), C("rewriteCost", ea, eb, alpha, beta))),
            E(C("Cstar", h), C("sup", C("univ", C("Fin", V("d"))),
                Seq(i, Mapsto, Sp, C("splitCost", h, i)))),
            All("K", N, Seq(C("InitialRewriteBudget", h, V("K")), Iff, Sp, P(initialBudget))))));
    }
    private static Formula UniformFormula()
    {
        Formula h = V("h"), c = V("C"), k = V("K"), ma = V("MA"), mb = V("MB");
        Formula body = All("a", V("A"), All("b", V("B"),
            All("word", List(C("Action", V("d"))),
                LE(C("Comm", C("step", c), C("cost", c),
                    C("initial", c, V("a"), V("b")), V("word")), k))));
        return Disp(SplitContext(All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"),
            All("C", C("Controller", h, ma, mb, V("Root")), All("K", N,
                Seq(C("UniformCumulativeBudget", c, k), Iff, Sp, P(body)))))))));
    }
    private static Formula BudgetFormula()
    {
        Formula d = V("d"), a = V("A"), b = V("B"), h = V("h"), c = V("C"), k = V("K");
        Formula ea = C("ell", a), eb = C("ell", b), star = C("Cstar", h), i = V("i");
        Formula trace = C("trace", c, C("rewrite", i), C("initial", c, V("a"), V("b")));
        Formula e = Pair(C("single", i, D(1)), D(0));
        Formula directions = All("a", a, All("b", b, All("i", C("Fin", d), A(
            LE(C("directionDemand", C("pA", e), eb), C("rightCount", trace)),
            LE(C("directionDemand", C("pB", e), ea), C("leftCount", trace))))));
        Formula universal = All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"),
            All("C", C("Controller", h, V("MA"), V("MB"), V("Root")), All("K", N,
            Imp(C("UniformCumulativeBudget", c, k), A(LE(star, k), directions)))))));
        Formula leastSet = Seq(OpenBrace, k, Colon, N, Mid, Sp, C("InitialRewriteBudget", h, k), CloseBrace);
        return Disp(SplitContext(Imp(A(LE(D(2), d), LT(D(0), C("finrank", Bit, a)),
            LT(D(0), C("finrank", Bit, b))), A(
            Imp(E(ea, D(0)), E(star, D(1))), Imp(E(eb, D(0)), E(star, D(1))),
            Imp(NE(ea, D(0)), Imp(NE(eb, D(0)), E(star, D(2)))),
            Ex("i", C("Fin", d), LT(D(0), C("splitCost", h, i))),
            C("IsLeast", leastSet, star), universal))));
    }

}
