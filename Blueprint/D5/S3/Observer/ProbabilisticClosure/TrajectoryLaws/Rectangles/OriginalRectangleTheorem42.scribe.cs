using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles;

internal sealed class OriginalRectangleTheorem42Document : IScribeDocumentDefinition
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
    private static Formula Some(string name, Formula type, Formula body) =>
        F.Seq(Exists, Sp, F.Id(name), Colon, Par(type), Comma, Sp, Par(body));
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
    private static Formula EndpointFormula()
    {
        var h = F.Id("H"); var theta = F.Id("theta"); var jlaw = F.Id("J");
        var d = F.Id("D"); var hc = F.Id("hc"); var w = F.Id("w");
        var rectangle = F.Id("R"); var r = F.Id("r"); var a = F.Id("a");
        var kappa = F.Id("kappa"); var klaw = F.Id("K"); var b = F.Id("b");
        var rho = F.Id("rho"); var eps = F.Id("epsilon"); var eta = F.Id("eta");
        var nat = F.Id("Nat"); var integer = F.Id("Int"); var boolean = F.Id("Bool");
        var zero = D(0); var one = D(1); var two = D(2);
        var hidden = Call("val", d); var card = Call("card", hidden);
        var z = F.Id("z"); var i = F.Id("i"); var jj = F.Id("j");
        var hh = F.Id("h"); var ss = F.Id("s"); var v = F.Id("v");
        var radius = F.Id("A"); var nn = F.Id("n"); var t = F.Id("t");
        var mass = Call("sum", Lam("i", hidden, Call("initial", theta, Call("val", i))));
        var product = Call("product", kappa, w);
        var headOne = Rel(Call("headOption", w), Eq, Call("some", F.Id("true")));
        var headZero = Rel(Call("headOption", w), Eq, Call("some", F.Id("false")));
        var route = Call("apply", a, hh);
        var visible = Call("visibleLaw", kappa);
        var outz = Call("snd", z);
        var x = F.Id("x");
        var bit = Lam("x", F.Seq(integer, To, Sp, boolean), Call("apply", x, zero));
        Formula Predictor(Formula obs) => Call("bitPredictor", visible, bit, obs, Call("apply", obs, outz));
        var q = Call("natDiv", jj, b);
        var leftCount = Call("chronologicalCount", w, b,
            Mul(F.Seq(Minus, Call("intCast", q)), Call("intCast", b)), q, z);
        var rightCount = Call("chronologicalCount", w, b, one, q, z);
        var pointwise = Call("AE", klaw, Lam("z", Call("PathSpace", hidden), Ands(
            Rel(Call("abs", MinusOf(Predictor(F.Id("exterior")),
                Predictor(Call("leftObservation", jj)))), Le, Pow(rho, leftCount)),
            Rel(Call("abs", MinusOf(Predictor(F.Id("exterior")),
                Predictor(Call("rightObservation", jj)))), Le, Pow(rho, rightCount)))));
        Formula PerRadius(Formula tails) => All("j", nat, Ands(
            Ands(Rel(zero, Le, rho), Rel(rho, Lt, one)),
            Ands(Rel(zero, Lt, eps), Rel(eps, Le, one)),
            Ands(Rel(zero, Le, eta), Rel(eta, Lt, one)),
            Ands(pointwise,
                Rel(Call("leftRisk", kappa, jj), Le, Pow(eta, q)),
                Rel(Call("rightRisk", kappa, jj), Le, Pow(eta, q))), tails));
        var sqrtEta = Call("sqrt", eta);
        var shifted = PlusOf(radius, nn);
        var rootTerms = Lam("n", nat, PlusOf(Call("sqrt", Call("leftRisk", kappa, shifted)),
            Call("sqrt", Call("rightRisk", kappa, shifted))));
        var tails = All("A", nat, Ands(
            Call("Summable", rootTerms),
            Rel(Call("rootErasureTail", kappa, radius), Le,
                Div(Mul(Mul(two, Call("realCast", b)), Pow(sqrtEta, Call("natDiv", radius, b))),
                    MinusOf(one, sqrtEta))),
            Rel(Call("erasureTail", kappa, radius), Le,
                Call("ofReal", Div(Mul(Mul(two, Call("realCast", b)),
                    Pow(eta, Call("natDiv", radius, b))), MinusOf(one, eta)))),
            Rel(Call("rootErasureTail", kappa, zero), Le,
                Div(Mul(two, Call("realCast", b)), MinusOf(one, sqrtEta)))));
        var conclusions = Ands(
            Rel(Call("length", Call("apply", a, r)), Eq, zero),
            All("h", hidden, Rel(Call("length", route), Le, card)),
            All("h", hidden, Imp(headZero, Rel(Call("length", route), Lt, card))),
            All("h", hidden, Imp(Rel(hh, Neq, r), Imp(headOne,
                Rel(Call("getLastOption", Call("ofFn", Call("labels", route))), Eq, Call("some", F.Id("false")))))),
            All("h", hidden, Call("Injective", Call("states", route))),
            Imp(headOne, All("s", hidden, Rel(Call("matrix", kappa, F.Id("true"), ss, r), Eq, zero))),
            All("t", integer, Rel(
                Call("smul", Call("ofReal", mass), Call("map", klaw, Call("componentInclusion", hidden))), Eq,
                Call("restrict", jlaw, Call("preimage", Call("state", t), Call("coeSet", hidden))))),
            All("v", Call("List", boolean), All("i", hidden, All("j", hidden,
                Rel(Call("productEntry", kappa, v, i, jj), Eq,
                    Call("productEntry", theta, v, Call("val", i), Call("val", jj)))))),
            Rel(Call("map", klaw, F.Id("snd")), Eq, visible), PerRadius(tails));
        var endpoint = Some("a", All("h", hidden, Call("LabelledRoute", kappa, hh, r)),
            Let("rho", MinusOf(one, Div(Call("rectangleMinimum", product, rectangle),
                Call("rectangleMaximum", product, rectangle))),
            Let("epsilon", Call("selectedEpsilon", kappa, w, r, a),
            Let("eta", MinusOf(one, Mul(eps, MinusOf(one, Pow(rho, two)))), conclusions))));
        endpoint = Let("kappa", Call("nativeComponent", theta, d, hc),
            Let("K", Call("jointLaw", kappa), Let("b", PlusOf(Call("length", w), card), endpoint)));
        endpoint = All("r", hidden, Imp(Rel(r, InMacro, Call("rows", rectangle)), endpoint));
        endpoint = All("R", Call("Rectangle", Call("product", Call("nativeComponent", theta, d, hc), w)), endpoint);
        endpoint = All("w", Call("List", boolean), Imp(Rel(w, Neq, Call("nil")), endpoint));
        endpoint = All("hc", Rel(zero, Lt, mass), endpoint);
        endpoint = All("D", Call("ClosedClass", PlusOf(Call("matrix", theta, F.Id("false")),
            Call("matrix", theta, F.Id("true")))), endpoint);
        endpoint = Imp(Call("HasOriginalCylinders", jlaw, theta), endpoint);
        endpoint = All("J", Call("Measure", Call("PathSpace", h)), F.Seq(
            OpenBracket, Call("IsProbabilityMeasure", jlaw), CloseBracket, endpoint));
        endpoint = All("theta", Call("Presentation", h), endpoint);
        return All("H", F.Id("Type"), Instances(h, endpoint));
    }
    private static Formula RootFormula()
    {
        var h = F.Id("H"); var theta = F.Id("theta"); var radius = F.Id("R");
        var n = F.Id("n"); var shifted = PlusOf(radius, n);
        return All("H", F.Id("Type"), Instances(h,
            All("theta", Call("Presentation", h), All("R", F.Id("Nat"),
                Rel(Call("rootErasureTail", theta, radius), Eq,
                    Call("tsum", Lam("n", F.Id("Nat"), PlusOf(
                        Call("sqrt", Call("leftRisk", theta, shifted)),
                        Call("sqrt", Call("rightRisk", theta, shifted))))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original rectangle theorem 4.2 native component consumer", H("Original rectangle theorem 4.2 native component consumer"),
        Blocks(
            Describe.Lean(DescribeId.Create("root-erasure-tail"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleTheorem42.rootErasureTail"),
                H("The actual sum of square roots of the two erasure risks"),
                StatementSource.FromAuthor(Disp(RootFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum is the real tsum of the square roots of the existing leftRisk and rightRisk. The theorem below separately proves summability of this exact series for every natural lower radius."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-component-rectangle-theorem42"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleTheorem42.native_component_rectangle_theorem42"),
                H("The original rectangle bounds and both geometric tails on one actual component"),
                StatementSource.FromAuthor(Disp(EndpointFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let theta be a finite original stationary binary edge presentation and J a probability measure with exactly theta's original marked integer-time cylinders. Let D be an actual closed communicating class of the support of M_0+M_1, with positive original stationary mass c, and let kappa be nativeComponent(theta,D,c-positive). Fix a nonempty Boolean word w and a rectangle R for product(kappa,w), with r in its row support. The hidden type in the conclusion is exactly the subtype D; kappa keeps the original matrix entries, normalizes the original stationary masses by c, and retains the scalar stationary no11 condition. The actual closed-class structure supplies irreducibility. Periodicity and structural zeros remain unrestricted, and the original scalar stationary no11 condition supplies the labelled-route seam.")),
                    Paragraph(Text("The theorem supplies a bounded positive labelled route family a from every h in D to r in the actual closed-class restriction. The route at r is empty. Each route has injective states and length at most card(D), with strict inequality when w starts with zero. When w starts with one, every nonempty selected route ends with a zero label and every incoming one-labelled matrix entry at r is zero. The occurrence probability uses the exact selectedEpsilon(kappa,w,r,a). The block length is b=length(w)+card(D); rho=1-u/v uses the minimum and maximum of the actual rectangle entries, and eta=1-epsilon*(1-rho^2).")),
                    Paragraph(Text("For every integer cut t, component_restriction identifies c times the inclusion pushforward of K=jointLaw(kappa) with J restricted to state(t) in D. For every Boolean word and every two states in D, the component word-product entry equals the original word-product entry. The output coordinate is unchanged by inclusion. The same law's visible pushforward K.map Prod.snd is identified with the existing visibleLaw(kappa) used by OriginalErasureComparison.leftRisk and rightRisk, so no convenient redefined risk or unrelated posterior law is introduced.")),
                    Paragraph(Text("For every j>=0, the finite posterior ratio is the existing bitPredictor conditional expectation on the exact finite record almost everywhere, after removing the union of null observation fibers; the ordered limits retain the entire opposite infinite half-line. The left and right pointwise defects are bounded under the same class law K=jointLaw(kappa) by rho raised to the chronological original b-block counts starting at -floor(j/b)*b and 1. Squaring and the chronological occurrence moment give leftRisk(kappa,j), rightRisk(kappa,j) <= eta^(floor(j/b)). The statement preserves j=0, rho=0, eta=0, and the natural 0^0=1 convention without division by rho or eta.")),
                    Paragraph(Text("For every natural R, the theorem asserts summability of the nonnegative root series, so its real sum represents the original tail. The public tail conclusion defines rootErasureTail(kappa,R) as the sum over j>=R of the square roots of the two existing risks and keeps erasureTail(kappa,R) as the existing sum of the two risks in extended reals. Existing OriginalUnifilarErasureTail.tail_series is consumed with rho=sqrt(eta) for the root tail and eta for the squared tail, yielding rootErasureTail(kappa,R) <= 2*b*(sqrt(eta))^(floor(R/b))/(1-sqrt(eta)), erasureTail(kappa,R) <= 2*b*eta^(floor(R/b))/(1-eta), and rootErasureTail(kappa,0) <= 2*b/(1-sqrt(eta)). The root numerator equals eta^((floor(R/b):Real)/2): the division by two is real division, including odd floor quotients. This identity uses nonnegativity, including eta=0. The endpoint and zero-rate cases remain in the same statement."))),
                DescribeRole.Theorem),
            Paragraph(Text("In the displayed formula, natDiv is natural division and realCast and intCast are the indicated canonical casts. headOption and getLastOption denote the list operations head? and getLast?, respectively. productEntry is the corresponding entry of product; sum over val(D) is the finite sum over the actual subtype D. AE(K,(z:T maps to p)) means p holds for K-almost every z:T. The displayed let expressions are abbreviations, not additional hypotheses. As in the Lean statement, the tail assertions occur inside the universal quantifier over j; they do not depend on j and hold for every natural lower radius, including zero. The finite hidden type has its given measurable space and measurable singletons; J is a probability measure. The class mass is the finite sum of the original initial weights over the subtype D.")),
            Paragraph(Text("The proof combines the same-law opposite-half-line posterior comparison with the chronological original-block moment bound. The component restriction identifies the actual conditioned joint law, irreducible labelled routes give the occurrence probability, and the geometric block series bounds both tails. The contraction and occurrence estimates act on the same original law throughout.")))));
}
