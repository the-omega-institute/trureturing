using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles;

internal sealed class OriginalRectanglePosteriorsDocument : IScribeDocumentDefinition
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
    private static Formula Div(Formula a, Formula b) => F.Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => F.Seq(Par(a), Caret, Grp(b));
    private static Formula Ands(params Formula[] terms)
    {
        Formula f = terms[0];
        for (int i = 1; i < terms.Length; i++) f = F.Seq(f, Land, Sp, Par(terms[i]));
        return f;
    }
    private static Formula Instances(Formula h, Formula body) => F.Seq(
        OpenBracket, Call("Fintype", h), CloseBracket,
        OpenBracket, Call("MeasurableSpace", h), CloseBracket,
        OpenBracket, Call("MeasurableSingletonClass", h), CloseBracket, body);

    private static Formula RangeFormula()
    {
        var h=F.Id("H"); var b=F.Id("B"); var r=F.Id("R");
        var rho=MinusOf(D(1), Div(Call("rectangleMinimum", b, r), Call("rectangleMaximum", b, r)));
        return All("H", F.Id("Type"), F.Seq(OpenBracket, Call("Fintype", h), CloseBracket,
            All("B", Call("Matrix", h, h, F.Id("Real")), All("R", Call("Rectangle", b),
                Ands(Rel(D(0), Le, rho), Rel(rho, Lt, D(1)))))));
    }
    private static Formula BoundsFormula()
    {
        var h=F.Id("H"); var theta=F.Id("theta"); var jlaw=F.Id("J");
        var w=F.Id("w"); var rectangle=F.Id("R"); var r=F.Id("r"); var a=F.Id("a");
        var j=F.Id("j"); var z=F.Id("z"); var nat=F.Id("Nat");
        var p=F.Id("P"); var b=F.Id("b"); var rho=F.Id("rho"); var eta=F.Id("eta"); var q=F.Id("q");
        var visible=F.Seq(F.Id("Int"), To, Sp, F.Id("Bool"));
        var x=F.Id("x"); var bit=Lam("x", visible, Call("apply", x, D(0)));
        Formula Predictor(Formula obs, Formula path) => Call("bitPredictor", p, bit, obs, Call("apply", obs, path));
        Formula Difference(Formula obs, Formula path) =>
            MinusOf(Predictor(F.Id("exterior"), path), Predictor(obs, path));
        var left=Call("leftObservation", j); var right=Call("rightObservation", j);
        var outz=Call("snd", z);
        var result=Ands(
            Call("AE", jlaw, Lam("z", Call("PathSpace", h), Ands(
                Rel(Call("abs", Difference(left, outz)), Le, Pow(rho,
                    Call("chronologicalCount", w, b, Mul(F.Seq(Minus, Call("intCast", q)), Call("intCast", b)), q, z))),
                Rel(Call("abs", Difference(right, outz)), Le, Pow(rho,
                    Call("chronologicalCount", w, b, D(1), q, z)))))),
            Rel(Call("integral", p, Lam("z", visible, Pow(Difference(left, z), D(2)))), Le, Pow(eta, q)),
            Rel(Call("integral", p, Lam("z", visible, Pow(Difference(right, z), D(2)))), Le, Pow(eta, q)));
        result=Let("P", Call("map", jlaw, F.Id("snd")),
            Let("b", PlusOf(Call("length", w), Call("card", h)),
            Let("rho", MinusOf(D(1), Div(Call("rectangleMinimum", Call("product", theta, w), rectangle),
                Call("rectangleMaximum", Call("product", theta, w), rectangle))),
            Let("eta", MinusOf(D(1), Mul(Call("selectedEpsilon", theta, w, r, a), MinusOf(D(1), Pow(rho, D(2))))),
            Let("q", Call("natDiv", j, b), result)))));
        result=All("j", nat, result);
        result=Imp(All("h", h, Rel(Call("length", Call("apply", a, F.Id("h"))), Le, Call("card", h))), result);
        result=All("a", All("h", h, Call("LabelledRoute", theta, F.Id("h"), r)), result);
        result=All("r", h, Imp(Rel(r, InMacro, Call("rows", rectangle)), result));
        result=All("R", Call("Rectangle", Call("product", theta, w)), result);
        result=All("w", Call("List", F.Id("Bool")), Imp(Rel(w, Neq, Call("nil")), result));
        result=Imp(Call("HasOriginalCylinders", jlaw, theta), result);
        result=All("J", Call("Measure", Call("PathSpace", h)), F.Seq(
            OpenBracket, Call("IsProbabilityMeasure", jlaw), CloseBracket, result));
        return All("H", F.Id("Type"), Instances(h, All("theta", Call("Presentation", h), result)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original rectangle posteriors and squared erasure defects", H("Original rectangle posteriors and squared erasure defects"),
        Blocks(
            Describe.Lean(DescribeId.Create("rectangle-rho-range"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectanglePosteriors.rectangle_rho_range"),
                H("The support rectangle gives a contraction parameter below one"),
                StatementSource.FromAuthor(Disp(RangeFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real matrix B on a finite index type and every positive support rectangle R, its least and greatest rectangle entries satisfy 0 < u <= v. Hence rho=1-u/v lies in [0,1), including rho=0. The same statement supplies the range in the posterior proof and the native component theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-rectangle-erasure-bounds"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectanglePosteriors.original_rectangle_erasure_bounds"),
                H("The finite ratios and chronological counts meet on the same original law"),
                StatementSource.FromAuthor(Disp(BoundsFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let H be any finite measurable hidden type with measurable singletons, theta an original stationary binary edge presentation, and J any probability measure on the original marked integer-time path space with HasOriginalCylinders(J,theta). Fix a nonempty Boolean word w, a support rectangle R for product(theta,w), a state r in its row support, and a family a(h) of positive labelled original routes from every hidden h to r, each of length at most card(H). Let j be any natural number. No hypothesis asserts a posterior bound, independence, future-conditioned occurrence, unifilarity, aperiodicity, or positivity outside the support rectangle.")),
                    Paragraph(Text("Define P=J.map(Prod.snd), b=length(w)+card(H), u=rectangleMinimum(product(theta,w),R), v=rectangleMaximum(product(theta,w),R), rho=1-u/v, epsilon=selectedEpsilon(theta,w,r,a), eta=1-epsilon*(1-rho^2), and q=j/b. Define q0, pL, and pR to be the total bounded OriginalErasureComparison.bitPredictor versions for the center bit under P, evaluated respectively on exterior=(before,after), leftObservation(j)=(leftWord(j),after), and rightObservation(j)=(before,rightWord(j)). bitPredictor_condExp identifies these versions almost everywhere with the corresponding P conditional expectations of erasedBit. Both before and after are the entire infinite half-lines. The theorem first asserts that, for J-almost every original marked path z, abs(q0(z.2)-pL(z.2)) is at most rho raised to chronologicalCount(w,b,-q*b,q,z), and abs(q0(z.2)-pR(z.2)) is at most rho raised to chronologicalCount(w,b,1,q,z). It then asserts that the P integral of (q0-pL)^2 and the P integral of (q0-pR)^2 are each at most eta^q. All three conclusions retain the same J and its exact visible pushforward P."))),
                DescribeRole.Theorem),
            Paragraph(Text("In the displayed formulas, integral(P,f) is the real integral of f under P; map, snd and intCast are the measure pushforward, second projection and canonical integer cast. natDiv is natural division, and AE(J,(z maps to p)) means p holds J-almost everywhere. All predictors use the same P and the center-bit map x maps to x(0).")),
            Paragraph(Text("The finite observation is the pair of chronological original words X[-k,-1] and X[1,n]. Its fiber at (a,c) is exactly OriginalRectangleSmoothing.record(List.ofFn(a),List.ofFn(c)). The alphabet is finite, so the union of zero-mass observation fibers is null, including when either word is empty. On every remaining fiber, Mathlib condDistrib_apply_of_ne_zero identifies the conditional distribution with the ratio of the center-true record mass to the full record mass. OriginalErasureComparison.bitPredictor_condExp identifies this ratio with the erasedBit conditional expectation given OriginalRectangleHalfLines.recordField(k,n). There is no division on a null record or hidden fiber.")),
            Paragraph(Text("For k>=j, the chronological left word splits as its earlier prefix followed by the retained j-bit suffix. For n>=j, the chronological right word splits as the retained j-bit prefix followed by the extra future. Those two decompositions are passed directly to finite_record_smoothing_by_original_success_count, using the positive long and short observed records. No reverse or extra-past kernel, transfer contraction, or likelihood matrix bound is reconstructed.")),
            Paragraph(Text("The recursive finite-list success count is identified by induction with the sum of the same visible block-success indicators in chronological order. In a sampled word of length n, each take(b) is the original b-bit block at the current integer start and each drop(b) advances that start by b. The trimmed left word has length (j/b)*b and begins at -j+(j mod b)=-(j/b)*b. The right word begins at 1; its final incomplete block is unused by the count. Thus for i from one through q the left blocks are [-q*b+(i-1)*b,-q*b+i*b-1] and the right blocks are [1+(i-1)*b,i*b]. Every success is a complete w-infix in that block's emitted bits, counted once. None includes X0.")),
            Paragraph(Text("finite_record_bounds_to_half_lines consumes the two finite conditional-expectation inequalities. It completes the past and then the future for left erasure, and the future and then the past for right erasure, without changing either count. Pullback by Prod.snd and the bitPredictor_condExp identities give the two bounds for the actual total bitPredictor versions under J. Squaring, changing variables between P and J, and applying chronological_success_moment at starts -q*b and 1 gives both squared-defect bounds with the original selected epsilon. Earlier blocks are paid in forward chronological time on each side; no lower bound after conditioning on a future is used. Integrability is obtained from bounded erasedBit and the conditional-expectation MemLp theorem, not from a claim that Mathlib's L1 martingale limit is an L2 theorem.")),
            Paragraph(Text("At j=0 the two counts are empty and the bound is one, while each observation retains the full opposite infinite half-line. Natural powers preserve rho=0 and 0^0=1. No step divides by rho or eta, so eta=0 is retained. Structural zeros remain governed by the existing positive-record supplier. This source is a reusable probability bridge for a supplied original-cylinder law and original route family. The native-component theorem instantiates theta and J with nativeComponent and the exact class-restricted original law via component_restriction; choose the original routes with irreducible_rectangle_occurrence; identify P with the exact visible law used by the native-component risk definitions; and use tail_series with eta and sqrt(eta) to give both original tails. OriginalRectangleTheorem42 states those native-component and tail conclusions."))
)));
}
