using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class NonlinearSelectorProfileDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Open, a, Close, Caret, Grp(b));

    private static Formula Statement()
    {
        var m = F.Id("m"); var k = F.Id("k"); var ell = F.Id("ell");
        var w = F.Id("w"); var r = F.Id("r"); var p = F.Id("p");
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var zero = Num(0); var one = Num(1); var two = Num(2);
        var twice = Multiply(two, m);
        var selector = Add(twice, one);
        var end = Add(Multiply(Num(3), m), one);
        var cut = Add(selector, ell);
        var remaining = Subtract(m, ell);
        var square = Pow(Pow(two, m), two);
        var doubled = Multiply(two, square);
        var c = Call("C", m);
        Formula Words(Formula len) => Call("Words", len);
        Formula Rs(Formula at) => Call("R", m, at);
        Formula Q(Formula at, Formula credit) => Call("Q", m, at, credit);
        Formula Card(Formula set) => Call("card", set);
        Formula Finite(Formula set) => Call("Finite", set);
        Formula Count(Formula set, Formula count) => And(Finite(set), Equal(Card(set), count));
        Formula Width(Formula labels) => Call("clog", two, labels);
        var k0 = Call("K0", m); var k1 = Call("K1", m);
        var singletonLanguages = new Formula.SetBuilder(Call("singleton", r), r, Words(remaining));
        var selectorPairs = new Formula.SetBuilder(Call("selectorPair", p), p,
            Product(Product(Words(m), Words(m)), F.Id("Bool")));
        var copyPairs = new Formula.SetBuilder(Call("copyPair", p), p,
            Product(F.Id("Bool"), Words(remaining)));
        var fixedLength = All("w", Call("List", F.Id("Bool")),
            Imp(Call("Member", w, c), Equal(Call("length", w), end)));
        return All("m", nat, Imp(Le(one, m), And(
            fixedLength, Call("Nonempty", c), Finite(c),
            All("k", nat, Imp(Le(k, twice), Count(Rs(k), Pow(two, k)))),
            All("ell", nat, Imp(Le(ell, m), And(
                Equal(Rs(cut), singletonLanguages),
                Count(Rs(cut), Pow(two, remaining))))),
            All("k", nat, Imp(And(Le(one, k), Le(k, twice)),
                Count(Q(k, one), Pow(two, k)))),
            Equal(Q(selector, one), selectorPairs), Count(Q(selector, one), doubled),
            All("ell", nat, Imp(And(Le(one, ell), Le(ell, m)), And(
                Equal(Q(cut, one), copyPairs),
                Count(Q(cut, one), Pow(two, Add(remaining, one)))))),
            All("k", nat, Imp(Le(k, end),
                Count(Q(k, zero), Card(Rs(k))))),
            Equal(k0, square), Equal(k1, doubled),
            Equal(Width(k0), twice), Equal(Width(k1), selector),
            Equal(Subtract(Width(k1), Width(k0)), one),
            Equal(Width(Card(Rs(selector))), m),
            Equal(Width(Card(Q(selector, one))), selector),
            Equal(Subtract(Width(Card(Q(selector, one))), Width(Card(Rs(selector)))), Add(m, one)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal binary selector relation has exact forward and one-credit profiles on its full actual carriers.",
        H("Exact Selector Family Profile"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-selector-family-profile"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/NonlinearSelectorProfile.exact_selector_family_profile"),
            H("Exact selector-family profile"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For each m at least one, C(m) consists exactly of i ++ j ++ [false] ++ i and i ++ j ++ [true] ++ j, where i and j are binary lists of length m. Every word has length 3m+1. Words(h) is the set of binary lists of length h. R(m,k) is residualSet(C(m),k), using completion residuals of actual prefixes. Q(m,k,d) is image(C(m),(k,d)) from StrictAnchoredBoundary, with the same actual prefixes, moving anchors, supplied actions and remaining credit.")),
                Paragraph(Text("The displayed selectorPair sends ((i,j),b) to ({false::i,true::j},[b]); copyPair sends (a,r) to ({a::r},[a]). singleton(r) denotes the language containing only r. Thus both range equations describe realized joint images and exclude additional pairs. After the selector and ell copied symbols, forward residuals are precisely all singleton suffixes of length m-ell. With positive ell and one credit, the anchor residual contains the newest symbol followed by that suffix, and the actual tail is exactly that newest symbol.")),
                Paragraph(Text("At preparation cuts, complete each prefix to two blocks using a common binary padding. If the completed first blocks differ, select false and copy the first block. If they agree, the second blocks differ; select true and copy the second block. The same completion is accepted from one prefix and rejected from the other. This proves distinct residuals for every binary preparation prefix, including cut zero and cut 2m. Every such prefix is extendable.")),
                Paragraph(Text("The strict anchored specialization supplies the actual joint-image equation and its finite sum over admissible tails. During preparation every anchor residual admits both one-symbol tails, giving the same count 2^k at credit one. At the selector the two first-symbol branches recover both blocks, and either selector bit is realized, giving 2 times (2^m)^2 points. After copying begins, the singleton residual and its first symbol determine exactly the joint point shown in copyPair. The terminal forward residual is the singleton empty word; the terminal one-credit image still distinguishes the last copied bit.")),
                Paragraph(Text("K0(m) is the maximum of card(R(m,k)) over 0 <= k <= 3m+1. K1(m) is the maximum of card(Q(m,k,d)) over the same cuts and 0 <= d <= min(1,k). The Lean definitions use finite suprema over exactly these integer ranges. Zero-credit images have exactly the forward residual count by the original supplier, so they are included in K1. There is no type (0,1). The forward maximum is attained at preparation cut 2m; the one-credit maximum is attained at selector cut 2m+1.")),
                Paragraph(Text("clog(2,N) is the ceiling binary logarithm of the finite label count N. The strict anchored specialization makes these counts the least conditional capacities for the supplied action contract. The peak binary widths are 2m and 2m+1, differing by one. At the selector alone the widths are m and 2m+1, differing by m+1. These are full-carrier counts conditional on an already supplied public type; they assign no acquisition, initialization, computation, transition-description or physical-memory cost."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ObserverMemory/StrictAnchoredBoundary"))]));
}
