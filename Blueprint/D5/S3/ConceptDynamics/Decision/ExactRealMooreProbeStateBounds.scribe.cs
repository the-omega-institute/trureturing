using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class ExactRealMooreProbeStateBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A globally correct fixed literal Moore probe table has at least four query rows "
            + "and at least six nominal rows.",
        H("Exact Real Moore Probe State Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-real-moore-probe-state-bounds"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds.nominal_lower_bounds"),
            H("Four query rows and six nominal rows are necessary"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/ConceptDynamics/magniez2013randomized")),
            Blocks(
                Paragraph(Text("P is an arbitrary finite type, in any universe. The fixed "
                    + "action map u assigns each row either one exact parameter in the closed "
                    + "unit interval or one literal Boolean Halt output. The fixed successor "
                    + "map v reads only the current row and the Boolean response. There is one "
                    + "fixed entry, independent of the source. The source is the entire unit "
                    + "interval times Bool, with no source probability law. At source (x,b), "
                    + "query a returns the complement of b when a equals x, and b otherwise. "
                    + "Queries leave the source unchanged.")),
                Paragraph(Text("CorrectEntry means that for each source separately, some "
                    + "finite fuel makes mooreRun stop at the first literal Halt with output b. "
                    + "There is no common fuel premise. Actual is a finite first-Halt trace "
                    + "retaining each issuing row, exact parameter and response, together with "
                    + "the terminal row. Its conversion to and from mooreRun preserves the "
                    + "ordered record. Folding only the responses reconstructs the current "
                    + "row and supplies the history policy used by the exact real probe cost "
                    + "theorem. That theorem gives an actual run with three different parameters.")),
                Paragraph(Text("QueryRows(u) in the displayed statement is the subtype of all "
                    + "p in P for which u(p) is a query, and card is its nominal cardinality. "
                    + "The proof also uses the finite set queryRows(u) with the same members. "
                    + "Unreachable rows, repeated query literals and repeated output literals "
                    + "remain in P. The transition table may contain cycles. A finite actual "
                    + "run on one fixed read-only source cannot repeat a query row, since its "
                    + "remaining deterministic behavior would then repeat forever.")),
                Paragraph(Text("Suppose there are at most three query rows. Parameter "
                    + "containment and the three-parameter run force exactly three such rows "
                    + "and make their literal parameters pairwise distinct. The entry A must "
                    + "query a. Either response at A is compatible with two opposite labels, "
                    + "so neither successor can be any literal Halt row. A successor equal to "
                    + "A repeats an actual query row and is also impossible.")),
                Paragraph(Text("If both responses at A lead to B, every original source "
                    + "reaches B after one query. The actual suffix is finite and correct for "
                    + "each source, so B is a globally correct entry. Prepending the A query "
                    + "to any correct B run shows that A cannot occur in that run. Only the "
                    + "two remaining query rows are available. Applying the three-parameter "
                    + "theorem at B contradicts this bound.")),
                Paragraph(Text("Otherwise write A:false to B and A:true to C, with literals "
                    + "a,c,d respectively. Sources (c,false) and (a,true) reach B after "
                    + "response false and both give response true at B, while requiring "
                    + "opposite outputs. A literal Halt successor fails one of them. A or B "
                    + "as successor repeats an actual row, so B:true must lead to C. Sources "
                    + "(c,false) and (d,true) now reach C with response false and opposite "
                    + "required outputs. Any Halt successor again fails one source; each "
                    + "query successor repeats a row already visited by (c,false). This "
                    + "exhausts every nominal successor and proves four query rows are necessary.")),
                Paragraph(Text("The correct first-Halt runs on (0,false) and (0,true) have "
                    + "terminal rows carrying different literal outputs, so those rows are "
                    + "distinct. Both lie outside the set of all query rows. Its union with "
                    + "these two rows therefore has at least six members and is contained in "
                    + "the full nominal carrier P. The different-parameter lower bound is "
                    + "reused from exact real probe costs. The additional row obstruction "
                    + "uses the fixed literal Moore actions and counts the Halt rows. "
                    + "This is a nominal control-state bound, not a physical storage-bit bound."))),
            DescribeRole.Theorem),
        Describe.Example(DescribeId.Create("exact-real-moore-history-borel"),
            H("The response-fold policy satisfies the original Borel contract"),
            ModelStatement(false, App("MeasurableStrategy", App("constantUnit", App("policy", F.Id("u"), F.Id("v"), F.Id("entry"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ConceptDynamics/magniez2013randomized")),
            Blocks(Paragraph(Text("P is arbitrary in any universe; no finiteness hypothesis is needed. The policy folds only Boolean responses over every finite ordered history, including impossible histories, and extends Halt by a stopped state. The Unit-indexed strategy has Borel controls at every record length and sourcewise measurable cost, finite-return and error events. This follows by composition with the finite Boolean response word at each record length.")))),
        GenericDescribe("exact-real-moore-source-cost-borel", "cost_source_borel",
            "Finite nominal tables have Borel cost on the entire original source",
            ModelStatement(true, App("Measurable", App("sourceCost", App("policy", F.Id("u"), F.Id("v"), F.Id("entry"))))),
            "P is finite, u and v are fixed literal maps, and entry is fixed. Source is the entire closed interval times Bool. sourceCost(pi) denotes the function sending an original source s to cost(pi,s). Cost counts distinct query parameters on the unique finite return and is infinite when no return exists. The finite response signature is a proof-side factorization, not a finite replacement of the source domain or a controller input."),
        GenericDescribe("exact-real-moore-return-event-borel", "terminal_event_source_borel",
            "Every finite-return record event is Borel on the original source",
            ModelStatement(true, Forall("E", App("Set", App("Product", F.Id("History"), F.Id("Bool"))),
                App("MeasurableSet", App("mooreReturnEvent", F.Id("u"), F.Id("v"), F.Id("entry"), F.Id("E"))))),
            "P is finite. For every set E of ordered records paired with outputs, mooreReturnEvent(u,v,entry,E) is the set of original sources s for which some natural fuel n and returned pair hb satisfy mooreRun(u,v,s,n,entry)=some(hb) and hb belongs to E. E has no extra measurability premise. No correctness, acyclicity or common fuel hypothesis is assumed."),
        Describe.Example(
            DescribeId.Create("exact-real-literal-six-row-attainer"),
            H("The literal six-row table attains the bound"),
            AttainerStatement(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/ConceptDynamics/magniez2013randomized")),
            Blocks(
                Paragraph(Text("The carrier LiteralRow consists of F, B0, B1, G, H0 and H1. "
                    + "The entry is F for every source. F queries 0 and sends false to B0 "
                    + "and true to B1. B0 queries 1/2 and sends false to H0 and true to G. "
                    + "B1 queries the same literal 1/2 and sends false to G and true to H1. "
                    + "G queries 1 and sends false to H0 and true to H1. H0 halts with false; "
                    + "H1 halts with true. Both Halt successors are their own row, and are "
                    + "unused after the first Halt. These are fixed literal real actions; "
                    + "no source name, history, clock or additional output port is read.")),
                Paragraph(Text("Write U for literalAction, V for literalNext, L(b) for "
                    + "literalHalt(b), T(s) for literalTrace(s), and R for records. "
                    + "The first tagged record is (F,0,response(0,s)); the second is "
                    + "(B1,1/2,response(1/2,s)) when the first response is true and "
                    + "(B0,1/2,response(1/2,s)) otherwise. The tagged record "
                    + "(G,1,response(1,s)) is appended exactly when the first two "
                    + "responses differ. The terminal row is L(b). Write C(s) for the "
                    + "natural number 2 plus the indicator that the coordinate of s is "
                    + "0 or 1/2, also coerced to the extended nonnegative reals when "
                    + "used as a cost. In the formula, Epi is the original finite-fuel "
                    + "execute response pi, M is mooreRun U V, pi is policy U V F, "
                    + "piThree is threeProbe(0,1/2,1), bit is the Boolean component, "
                    + "and parameters is the finite set of distinct literal query values.")),
                Paragraph(Text("For every original (x,b) in the whole closed interval times "
                    + "Bool, T(s) is an actual finite first-Halt trace. If x is outside "
                    + "{0,1/2}, its responses are b,b, and the table stops after two "
                    + "queries. If x is 0, its responses are complement(b),b,b; if x is "
                    + "1/2, they are b,complement(b),b. In both exceptional cases the "
                    + "table queries 1 and stops after three queries. The returned output "
                    + "is b in every case. Fuel four suffices for this construction; "
                    + "that bound is a consequence and is not a premise on competing tables.")),
                Paragraph(Text("At every fuel the original threeProbe execution and this "
                    + "Moore execution agree on the same source, preserving the ordered "
                    + "literal query-response record and first stopping output. Every "
                    + "actual first-Halt trace agrees with T(s), including its terminal "
                    + "row. The cost is the number of distinct parameters in that record, "
                    + "equal to C(s), at most three, and exactly three at (0,false). "
                    + "Four nominal query rows and six total rows count both midpoint "
                    + "rows and both literal output rows.")),
                Paragraph(Text("W(p) in the formula is the explicit source literalWitness(p): "
                    + "(1,false) for F, B0 and H0; (1,true) for B1 and H1; and (0,false) "
                    + "for G. The empty prefix witnesses F. The first query reaches B0 "
                    + "or B1; the first two queries reach H0 or H1 on their stated sources. "
                    + "On (0,false), the prefix F then B1 reaches G. Each prefix has an "
                    + "actual finite continuation to the first Halt, including the empty "
                    + "continuation at a Halt row.")),
                Paragraph(Text("The policy folds only Boolean responses over the entire "
                    + "original history space and keeps Halt rows stopped. Equal response "
                    + "words give equal actions, including on histories that never occur. "
                    + "On each actual prefix, its action is the current row's literal "
                    + "action. Each fixed record length has a Borel control map. The "
                    + "input-independent Unit strategy satisfies the original sourcewise "
                    + "cost and finite return/error event measurability contract. Cost "
                    + "is also Borel as a function of the original source, and every "
                    + "finite-return record/output event is Borel. Agreement with "
                    + "threeProbe is asserted on actual executions; no equality on "
                    + "impossible or post-Halt histories is required.")))))));

    private static DocumentBlock GenericDescribe(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds." + declaration),
            H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ConceptDynamics/magniez2013randomized")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula ModelStatement(bool finite, Formula body)
    {
        var p = F.Id("P");
        var model = Forall("u", new Formula.TypeArrow(p, App("Sum", F.Id("I"), F.Id("Bool"))),
            Forall("v", new Formula.TypeArrow(p, new Formula.TypeArrow(F.Id("Bool"), p)),
                Forall("entry", p, body)));
        return Disp(Forall("P", "Type", finite ? Implies(App("Finite", p), model) : model));
    }

    private static Formula App(string name, params Formula[] args) => Call(name, args);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Forall(string name, string type, Formula body) =>
        Forall(name, F.Id(type), body);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Statement()
    {
        var p = F.Id("P");
        var u = F.Id("u");
        var v = F.Id("v");
        var entry = F.Id("entry");
        return Disp(Forall("P", "Type", Implies(App("Finite", p),
            Forall("u", new Formula.TypeArrow(p, App("Sum", F.Id("I"), F.Id("Bool"))),
                Forall("v", new Formula.TypeArrow(p,
                    new Formula.TypeArrow(F.Id("Bool"), p)),
                    Forall("entry", p, Implies(App("CorrectEntry", u, v, entry),
                        And(Le(Num(4), App("card", App("QueryRows", u))),
                            Le(Num(6), App("card", p))))))))));
    }
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Conjoin(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i) result = And(clauses[i], result);
        return result;
    }
    private static Formula AttainerStatement()
    {
        var u = F.Id("U"); var v = F.Id("V"); var f = F.Id("F");
        var s = F.Id("s"); var n = F.Id("n"); var p = F.Id("p");
        var rs = F.Id("rs"); var q = F.Id("q"); var b = F.Id("b");
        var pre = F.Id("pre"); var tail = F.Id("tail");
        var h = F.Id("h"); var k = F.Id("k"); var e = F.Id("E");
        var pi = F.Id("pi"); var piThree = F.Id("piThree");
        var bit = App("bit", s); var trace = App("T", s); var record = App("R", trace);
        var halt = App("L", bit); var c = App("C", s);
        Formula Run(Formula policy, Formula fuel, Formula source) =>
            App("Epi", policy, fuel, App("nil"), source);
        Formula Moore(Formula fuel) => App("M", s, fuel, f);
        Formula Cost(Formula source) => App("cost", pi, source);
        var actual = App("Actual", u, v, s, f, rs, q, b);
        var allActual = Forall("rs", App("ListTagged", F.Id("LiteralRow")),
            Forall("q", "LiteralRow", Forall("b", "Bool", Implies(actual,
                Conjoin(Eq(App("R", rs), record), Eq(q, halt), Eq(b, bit),
                    Eq(App("card", App("parameters", App("R", rs))), c))))));
        var sourceClauses = Forall("s", "Source", Conjoin(
            App("Actual", u, v, s, f, trace, halt, bit),
            Eq(Moore(Num(4)), App("some", App("pair", record, bit))),
            Forall("n", "Nat", Eq(Run(piThree, n, s), Moore(n))),
            Eq(Cost(s), c), allActual));
        var w = App("W", p);
        var reach = Forall("p", "LiteralRow",
            Exists("pre", App("ListTagged", F.Id("LiteralRow")),
                Exists("tail", App("ListTagged", F.Id("LiteralRow")),
                    Exists("q", F.Id("LiteralRow"), And(
                        App("Prefix", u, v, w, f, pre, p),
                        App("Actual", u, v, w, p, tail, q, App("bit", w)))))));
        var prefixAction = Forall("s", "Source",
            Forall("pre", App("ListTagged", F.Id("LiteralRow")),
                Forall("p", "LiteralRow", Implies(App("Prefix", u, v, s, f, pre, p),
                    Eq(App("pi", App("R", pre)), App("U", p))))));
        var causal = Forall("h", "History", Forall("k", "History",
            Implies(Eq(App("responses", h), App("responses", k)),
                Eq(App("pi", h), App("pi", k)))));
        var events = Forall("E", App("Set", App("Product", F.Id("History"), F.Id("Bool"))),
            App("MeasurableSet", App("returnEvent", pi, e)));
        return Disp(Conjoin(App("CorrectEntry", u, v, f), sourceClauses, reach,
            Eq(App("card", App("queryRows", u)), Num(4)),
            Eq(App("card", F.Id("LiteralRow")), Num(6)), prefixAction, causal,
            App("MeasurableStrategy", App("constantUnit", pi)),
            App("Measurable", App("sourceCost", pi)), events,
            Forall("s", "Source", Le(Cost(s), Num(3))),
            Eq(Cost(App("pair", Num(0), App("false"))), Num(3))));
    }

}
