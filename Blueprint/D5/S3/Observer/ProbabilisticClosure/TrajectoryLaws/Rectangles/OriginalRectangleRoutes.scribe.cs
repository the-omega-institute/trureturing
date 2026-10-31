using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles;

internal sealed class OriginalRectangleRoutesDocument : IScribeDocumentDefinition
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
    private static Formula Let(string name, Formula value, Formula body) =>
        F.Seq(F.Id("let"), Sp, F.Id(name), Colon, Eq, value, Semi, Sp, body);
    private static Formula Rel(Formula a, Formula relation, Formula b) => F.Seq(a, relation, Sp, b);
    private static Formula Imp(Formula a, Formula b) => F.Seq(Par(a), Implies, Sp, Par(b));
    private static Formula PlusOf(Formula a, Formula b) => F.Seq(Par(a), Plus, Par(b));
    private static Formula Mul(Formula a, Formula b) => F.Seq(Par(a), Cdot, Sp, Par(b));
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

    private static Formula RoutesFormula()
    {
        var h=F.Id("H"); var theta=F.Id("theta"); var jlaw=F.Id("J");
        var w=F.Id("w"); var rectangle=F.Id("R"); var r=F.Id("r"); var a=F.Id("a");
        var hh=F.Id("h"); var t=F.Id("t"); var eventA=F.Id("A"); var card=Call("card", h);
        var eps=F.Id("epsilon"); var b=F.Id("b"); var nat=F.Id("Nat"); var integer=F.Id("Int");
        var route=Call("apply", a, hh);
        var headOne=Rel(Call("headOption", w), Eq, Call("some", F.Id("true")));
        var headZero=Rel(Call("headOption", w), Eq, Call("some", F.Id("false")));
        var stateEvent=Call("preimage", Call("state", t), Call("singleton", hh));
        var pastEvent=Call("preimage", Call("past", t), eventA);
        var jointPast=Call("inter", stateEvent, pastEvent);
        var paid=Ands(Rel(D(0), Lt, eps), Rel(eps, Le, D(1)),
            All("t", integer, All("h", h, Imp(Rel(D(0), Lt, Call("initial", theta, hh)),
                Rel(Call("ofReal", eps), Le, Call("measureApply", Call("futureLaw", jlaw, t, hh), Call("success", w, b)))))),
            All("t", integer, All("h", h, All("A", Call("Set", Call("MarkedPast", h)),
                Imp(Call("MeasurableSet", eventA), Rel(Mul(Call("ofReal", eps), Call("measureApply", jlaw, jointPast)), Le,
                    Call("measureApply", jlaw, Call("inter", jointPast,
                        Call("preimage", Call("future", t), Call("success", w, b))))))))));
        paid=Let("epsilon", Call("selectedEpsilon", theta, w, r, a),
            Let("b", PlusOf(Call("length", w), card), paid));
        var result=Some("a", All("h", h, Call("LabelledRoute", theta, hh, r)), Ands(
            Rel(Call("length", Call("apply", a, r)), Eq, D(0)),
            All("h", h, Rel(Call("length", route), Le, card)),
            All("h", h, Imp(headZero, Rel(Call("length", route), Lt, card))),
            All("h", h, Imp(Rel(hh, Neq, r), Imp(headOne,
                Rel(Call("getLastOption", Call("ofFn", Call("labels", route))), Eq, Call("some", F.Id("false")))))),
            All("h", h, Call("Injective", Call("states", route))),
            Imp(headOne, All("s", h, Rel(Call("matrix", theta, F.Id("true"), F.Id("s"), r), Eq, D(0)))), paid));
        result=All("r", h, Imp(Rel(r, InMacro, Call("rows", rectangle)), result));
        result=All("R", Call("Rectangle", Call("product", theta, w)), result);
        result=All("w", Call("List", F.Id("Bool")), result);
        var i=F.Id("i"); var j=F.Id("j"); var n=F.Id("n");
        var irreducible=All("i", h, All("j", h, Some("n", nat,
            Rel(D(0), Lt, Call("entry", Pow(PlusOf(Call("matrix", theta, F.Id("false")),
                Call("matrix", theta, F.Id("true"))), n), i, j)))));
        result=Imp(irreducible, result);
        result=Imp(Call("HasOriginalCylinders", jlaw, theta), result);
        result=All("J", Call("Measure", Call("PathSpace", h)), F.Seq(
            OpenBracket, Call("IsProbabilityMeasure", jlaw), CloseBracket, result));
        return All("H", F.Id("Type"), Instances(h, All("theta", Call("Presentation", h), result)));
    }

    private static Formula SeamFormula()
    {
        var h=F.Id("H"); var theta=F.Id("theta"); var jlaw=F.Id("J");
        var w=F.Id("w"); var rectangle=F.Id("R"); var r=F.Id("r");
        var t=F.Id("t"); var z=F.Id("z"); var i=F.Id("i"); var j=F.Id("j");
        var n=F.Id("n"); var integer=F.Id("Int");
        var eventBody=Ands(Rel(Call("state", t, z), Eq, r),
            Rel(Call("apply", Call("snd", z), F.Seq(t, Minus, D(1))), Eq, F.Id("true")));
        var eventSet=Call("setOf", F.Seq(Open, z, Colon, Call("PathSpace", h),
            Mapsto, Sp, eventBody, Close));
        var result=All("t", integer, Rel(Call("measureApply", jlaw, eventSet), Eq, D(0)));
        result=Imp(Rel(Call("headOption", w), Eq, Call("some", F.Id("true"))), result);
        result=All("r", h, Imp(Rel(r, InMacro, Call("rows", rectangle)), result));
        result=All("R", Call("Rectangle", Call("product", theta, w)), result);
        result=All("w", Call("List", F.Id("Bool")), result);
        var irreducible=All("i", h, All("j", h, Some("n", F.Id("Nat"),
            Rel(D(0), Lt, Call("entry", Pow(PlusOf(Call("matrix", theta, F.Id("false")),
                Call("matrix", theta, F.Id("true"))), n), i, j)))));
        result=Imp(irreducible, result);
        result=Imp(Call("HasOriginalCylinders", jlaw, theta), result);
        result=All("J", Call("Measure", Call("PathSpace", h)), F.Seq(
            OpenBracket, Call("IsProbabilityMeasure", jlaw), CloseBracket, result));
        return All("H", F.Id("Type"), Instances(h, All("theta", Call("Presentation", h), result)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simple original routes to a rectangular word", H("Simple original routes to a rectangular word"),
        Blocks(Describe.Lean(DescribeId.Create("irreducible-rectangle-occurrence"),
            DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.irreducible_rectangle_occurrence"),
            H("Irreducibility pays the visible word occurrence on the original law"),
            StatementSource.FromAuthor(Disp(RoutesFormula())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let H be any finite measurable hidden state type with measurable singletons, theta a stationary nonnegative binary edge presentation with its original scalar no11 condition, and J a probability measure with exactly theta's original integer-time marked cylinders. Assume irreducibility in the form that every pair of states has a positive entry in some nonnegative natural power of M0 plus M1. Let w be a binary list with nonempty rectangular positive matrix support, and r a support row. There exists a selected positive original labelled route from every h to r, with an injective list of hidden vertices. The route from r is empty and has weight one. Every route has at most card(H) edges; when the word begins with zero, every route has strictly fewer than card(H) edges. If the word begins with one and h differs from r, the last selected edge is labelled zero. For precisely these selected routes, epsilon is their exact minimum pathMass multiplied by the row sum of the original word product at r, and b is length(w) plus card(H). Epsilon is strictly positive and at most one. At every integer cut and every positive hidden fiber, the actual conditional future kernel assigns the one common visible success(w,b) event probability at least epsilon. For every hidden state, including a null fiber, and every measurable event A of the entire marked past, ENNReal.ofReal(epsilon) times J of state=h and past in A is at most J of that event together with future in success(w,b). The selected routes, visible event and conditional probabilities all belong to this same original J.")),
                Paragraph(Text("The route construction directly reuses the pinned shortestPath and shortest_path_spec APIs and the existing quiver isStrictlySimple_of_shortest and simple-path cardinality theorems. The original matrix-power support API supplies reachability, while label extraction preserves the complete vertex list. Simplicity therefore survives the assignment of positive original Boolean emission labels. For a word beginning with one, positivity of its support row gives a positive one-labelled outgoing edge at r. Original scalar no11, applied through positive-state trimming and the irreducible stationary masses, makes every one-labelled incoming entry at r zero. The final edge of a nonempty positive simple route into r is consequently labelled zero, with no appended detour. Injectivity makes the route from r empty. The same incoming-zero property also excludes a just-emitted one on an actual past arriving at r in the empty-prefix case. For a word beginning with zero, no incoming-label restriction is needed. The occurrence estimate directly reuses original_rectangle_occurrence with precisely these selected routes and their exact selectedEpsilon. It is a prerequisite of source Theorem 4.2, and does not assert either full-half-line erasure inequality, adapted success-count payment, or any root or squared-tail constant. Source Section 7 still requires those full bounds for its loss-cocycle and second-order localization applications."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-one-incoming-past-null"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.first_one_incoming_past_null"),
                H("The empty-prefix incoming-past seam is null"),
                StatementSource.FromAuthor(Disp(SeamFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let H be any finite measurable hidden type with measurable singletons, theta an original stationary nonnegative binary edge presentation satisfying only its scalar no11 condition, and J any probability with theta's original marked cylinders. Assume every pair of states has a positive entry in some natural power of M0 plus M1. For any rectangle word w beginning with one, any positive support row r, and every integer cut d, J of the event H(d)=r and X(d-1)=one is zero. Irreducible stationary masses are positive, and the existing scalar-no11 trimming argument gives zero for every incoming one-labelled entry at r. The forbidden event is contained in the finite union of original one-edge cylinders ending at r with label one; each has exactly zero original cylinder mass. This proves a statement about actual past trajectories, rather than just a matrix-entry statement.")),
                    Paragraph(Text("For an actual positive-weight source class C, apply this result to nativeComponent with its unchanged original matrix entries and actual original-cylinder law K. Inclusion sends the null statement to the identical event on the original H/output carrier of J_C. The indicator of that event is almost everywhere zero, so its conditional expectation on the complete original marked-past sigma-field is zero as well. For the given empty route a(r), length zero gives pathMass exactly one. Thus a source word beginning with one has no positive-mass incoming-past conflict at the empty-prefix seam. Stationarity, positivity of the mass at r and the incoming-one zeros also give a positive zero-labelled predecessor; a simple route ending at r has a final zero edge. All conclusions stay inside the actual positive class. No global entrywise M1-squared-zero hypothesis is added."))),
                DescribeRole.Theorem))));
}
