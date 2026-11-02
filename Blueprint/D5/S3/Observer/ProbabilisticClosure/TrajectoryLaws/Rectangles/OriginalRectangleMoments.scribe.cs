using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles;

internal sealed class OriginalRectangleMomentsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args)
    {
        Formula f = F.Seq(Operatorname, Grp(F.Id(name)), Open);
        for (int i = 0; i < args.Length; i++)
            f = i == 0 ? F.Seq(f, args[i]) : F.Seq(f, Comma, Sp, args[i]);
        return F.Seq(f, Close);
    }
    private static Formula Par(Formula f) => F.Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(Forall, Sp, F.Id(name), Colon, Par(type), Comma, Sp, Par(body));
    private static Formula Lam(string name, Formula type, Formula body) =>
        F.Seq(Open, F.Id(name), Colon, type, Mapsto, Sp, body, Close);
    private static Formula Let(string name, Formula value, Formula body) =>
        F.Seq(F.Id("let"), Sp, F.Id(name), Colon, Eq, value, Semi, Sp, body);
    private static Formula Rel(Formula a, Formula relation, Formula b) => F.Seq(a, relation, Sp, b);
    private static Formula Imp(Formula a, Formula b) => F.Seq(Par(a), Implies, Sp, Par(b));
    private static Formula PlusOf(Formula a, Formula b) => F.Seq(Par(a), Plus, Par(b));
    private static Formula MinusOf(Formula a, Formula b) => F.Seq(Par(a), Minus, Par(b));
    private static Formula Mul(Formula a, Formula b) => F.Seq(Par(a), Cdot, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => F.Seq(Par(a), Caret, Grp(b));
    private static Formula Instances(Formula h, Formula body) => F.Seq(
        OpenBracket, Call("Fintype", h), CloseBracket,
        OpenBracket, Call("MeasurableSpace", h), CloseBracket,
        OpenBracket, Call("MeasurableSingletonClass", h), CloseBracket, body);

    private static Formula MomentFormula(string selector)
    {
        var h=F.Id("H"); var theta=F.Id("theta"); var jlaw=F.Id("J");
        var w=F.Id("w"); var rectangle=F.Id("R"); var r=F.Id("r"); var a=F.Id("a");
        var b=F.Id("b"); var d=F.Id("d"); var q=F.Id("q"); var z=F.Id("z"); var t=F.Id("t");
        var nat=F.Id("Nat"); var integer=F.Id("Int"); var real=F.Id("Real");
        var list=Call("List", F.Id("Bool")); var path=Call("PathSpace", h);
        if (selector == "markedField")
            return All("H", F.Id("Type"), F.Seq(OpenBracket, Call("MeasurableSpace", h), CloseBracket,
                All("t", integer, Rel(Call("markedField", t), Eq, Call("generatedField",
                    Lam("z", path, Call("pair", Call("state", t, z), Call("past", t, z))))))));
        if (selector == "blockSuccess")
            return All("H", F.Id("Type"), All("w", list, All("b", nat, All("d", integer,
                Rel(Call("blockSuccess", h, w, b, d), Eq,
                    Call("preimage", Call("future", h, d), Call("success", w, b)))))));
        if (selector == "chronologicalCount")
        {
            var i=F.Id("i");
            var start=PlusOf(d, Mul(Call("intCast", i), Call("intCast", b)));
            var count=Call("sumRange", q, Lam("i", nat,
                Call("ite", Rel(z, InMacro, Call("blockSuccess", w, b, start)), D(1), D(0))));
            return All("H", F.Id("Type"), All("w", list, All("b", nat, All("d", integer,
                All("q", nat, All("z", path,
                    Rel(Call("chronologicalCount", w, b, d, q, z), Eq, count)))))));
        }
        Formula result;
        var eps=Call("selectedEpsilon", theta, w, r, a);
        var block=PlusOf(Call("length", w), Call("card", h));
        if (selector == "marked_success_condExp")
            result=All("t", integer, Call("AE", jlaw, Lam("z", path,
                Rel(eps, Le, Call("condExp", jlaw,
                    Call("indicator", Call("blockSuccess", w, block, t), Call("constFunction", path, D(1))),
                    Call("markedField", t), z)))));
        else if (selector == "chronological_success_moment")
        {
            var rho=F.Id("rho"); var eta=F.Id("eta");
            result=Rel(Call("integral", jlaw, Lam("z", path,
                Pow(rho, Mul(D(2), Call("chronologicalCount", w, b, d, q, z))))), Le, Pow(eta, q));
            result=Let("b", block, Let("eta", MinusOf(D(1), Mul(eps, MinusOf(D(1), Pow(rho, D(2))))), result));
            result=All("rho", real, Imp(Rel(D(0), Le, rho), Imp(Rel(rho, Le, D(1)),
                All("d", integer, All("q", nat, result)))));
        }
        else throw new System.ArgumentException("Unknown mathematical declaration", nameof(selector));
        result=Imp(All("h", h, Rel(Call("length", Call("apply", a, F.Id("h"))), Le, Call("card", h))), result);
        result=All("a", All("h", h, Call("LabelledRoute", theta, F.Id("h"), r)), result);
        result=All("r", h, Imp(Rel(r, InMacro, Call("rows", rectangle)), result));
        result=All("R", Call("Rectangle", Call("product", theta, w)), result);
        result=All("w", list, result);
        result=Imp(Call("HasOriginalCylinders", jlaw, theta), result);
        result=All("J", Call("Measure", path), F.Seq(OpenBracket, Call("IsProbabilityMeasure", jlaw), CloseBracket, result));
        return All("H", F.Id("Type"), Instances(h, All("theta", Call("Presentation", h), result)));
    }

    private static DocumentBlock.Describe Entry(string id, string selector, string heading, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleMoments." + selector),
            H(heading), StatementSource.FromAuthor(Disp(MomentFormula(selector))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological rectangle occurrence moments", H("Chronological rectangle occurrence moments"),
        Blocks(
            Entry("marked-field", "markedField", "The complete original marked past at a cut",
                "For any measurable hidden type H and integer t, markedField(t) is the sigma-field generated by the pair consisting of H(t) and the entire sequence of hidden states and emitted bits strictly before t. It contains every hidden coordinate through t and every output coordinate below t. It contains no output at t or later.", DescribeRole.Definition),
            Entry("block-success", "blockSuccess", "One success depends only on the block's emitted bits",
                "blockSuccess(w,b,d) is the original event that w is an infix of the b consecutive emitted bits beginning at integer d. It is the preimage of OriginalRectangleOccurrence.success(w,b) under the original future(d) map. Hidden starting states do not enter this event.", DescribeRole.Definition),
            Entry("chronological-count", "chronologicalCount", "The original chronological block count",
                "chronologicalCount(w,b,d,q) is the sum of the success indicators for the q disjoint blocks beginning at d, d+b, through d+(q-1)b, in that time order. Each block pays once, regardless of how many occurrences lie inside it. An empty block sequence has count zero.", DescribeRole.Definition),
            Entry("marked-success-condexp", "marked_success_condExp", "The same-law conditional success probability",
                "Let theta be any original stationary binary edge presentation on finite measurable H, and J any probability measure with theta's original marked cylinders. Fix a Boolean word w, a support rectangle for product(theta,w), a row r in its row support, and the given family a of positive labelled original routes from every h to r, each of length at most card(H). Set b=length(w)+card(H), and keep exactly the selectedEpsilon(theta,w,r,a) of that family. For every integer t, the conditional expectation under J of the blockSuccess(w,b,t) indicator given markedField(t) is at least this epsilon almost everywhere. The complete marked-past occurrence inequality is summed over the finite hidden fibers for an arbitrary measurable event of markedField(t). Its real integral characterization then gives the conditional-expectation lower bound. Null hidden fibers remain in the sum and require no division.", DescribeRole.Theorem),
            Entry("chronological-success-moment", "chronological_success_moment", "Successes pay the squared contraction in chronological time",
                "Under the same presentation, same original-cylinder probability J, same word, rectangle, support row and given route family as above, take any real rho with 0<=rho<=1, any integer start d and natural block count q. Let b=length(w)+card(H), epsilon=selectedEpsilon(theta,w,r,a), eta=1-epsilon*(1-rho^2), and K=chronologicalCount(w,b,d,q). The J integral of rho^(2*K) is at most eta^q. The single-block factor is rho^2 on success and one otherwise. Its conditional expectation at the block start is at most eta by the preceding conditional probability bound. All earlier factors are measurable in the complete marked past at the next block start; pulling them out and taking total expectation gives one factor eta at each step. No independence, future-conditioned success estimate, positivity of every matrix entry, aperiodicity or unifilarity is imposed. The case q=0 is the integral of one, including rho=0; eta may also be zero.", DescribeRole.Theorem),
            Paragraph(Text("The blockSuccess defining equality displays its implicit hidden type H explicitly in blockSuccess(H,w,b,d) and future(H,d). In the formulas, generatedField(f) means the comap of the canonical product measurable space along f; condExp(J,f,m,z) is the conditional expectation of f given m evaluated at z. sumRange(q,f) is the natural finite sum over i in Finset.range(q); indicator(S,f), constFunction(T,c), preimage, integral and intCast have their corresponding Lean meanings. AE(J,(z maps to p)) denotes the almost-everywhere quantifier under J.")),
            Paragraph(Text("For a native source component C, instantiate theta with nativeComponent and use the very original-cylinder law on C identified by component_restriction. Choose the routes furnished by OriginalRectangleRoutes, without changing the selected family or its epsilon. Put rho=1-u/v from the original support rectangle. For q=floor(j/b), the left count uses d=-q*b and the right count uses d=1. These are respectively the source blocks [-q*b+(i-1)b,-q*b+i*b-1] and [1+(i-1)b,i*b], for i from one through q. Both applications average in chronological original time under this one class-restricted measure, even though the finite right-posterior comparison propagates in reverse. At j=0 both block counts are empty. The identity with the finite-list count in finite_record_smoothing_by_original_success_count and the identification of finite-record posteriors with conditional expectations supply the separate connections from posterior differences to these moments.")))));
}
