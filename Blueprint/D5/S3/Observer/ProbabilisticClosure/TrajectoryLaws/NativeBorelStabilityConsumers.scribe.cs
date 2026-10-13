using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelStabilityConsumersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.";

    public DocumentDefinition Create()
    {

        Formula flow = F.Id("F"), u = F.Id("U"), mu = F.Id("mu"), b = F.Id("b"), n = F.Id("n");
        Formula nu = F.Id("nu"), s = F.Id("s"), d = F.Id("D");
        Formula z = Call("zR", b), c = Call("cR", b), rho = Call("radiusP");
        Formula supported = And(Call("positiveDepthOne", mu), Call("positiveDepthTwo", mu));
        Formula J = Call("supportedRisk", Call("flowMargins", flow), mu);
        Formula risk = All(Imp(supported, Imp(Le(Num(4), n),
            Le(rho, Add(J, Times(Call("HR", b), Fraction(Call("slack", flow, b, n), Times(c, Pow(z, n)))))))),
            ("F", "CommonFlow"), ("mu", "DepthPMF"), ("b", "Bool"), ("n", "Nat"));
        Formula boxes = All(Imp(Call("probabilityMargins", nu), Imp(supported,
            Imp(Equal(Call("supportedRisk", nu, mu), Num(0)),
                Ae(Call("margin", nu, s), d, Call("EndpointBox", d))))),
            ("nu", "PhaseMargins"), ("mu", "DepthPMF"), ("s", "ActivePhase"));
        Formula midpoint = Equal(Call("pEventMean", flow), Fraction(Num(11758471), Num(22781250)));
        Formula midpointLoss = All(Imp(midpoint, Equal(Call("pMeanLoss", flow, b), rho)),
            ("F", "CommonFlow"), ("b", "Bool"));
        Formula interval(Formula f) => And(
            Le(Times(Times(Fraction(Num(4), Num(9)), Pow(Fraction(Num(2), Num(9)), n)),
                Add(Num(1), Fraction(rho, Fraction(Num(9839648), Num(2657205))))), Call("meanCoordinate", f, n)),
            Le(Call("meanCoordinate", f, n), Times(Times(Fraction(Num(9), Num(25)), Pow(Fraction(Num(6), Num(25)), n)),
                Sub(Num(1), Fraction(rho, Fraction(Num(20723912), Num(5859375)))))));
        Formula midInterval = All(Imp(midpoint, Imp(Le(Num(4), n), interval(flow))),
            ("F", "CommonFlow"), ("n", "Nat"));
        Formula zero = Equal(Call("supportedRisk", Call("unboxedMargins", u), mu), Num(0));
        Formula boxed = Call("zeroFace", u, mu);
        Formula zeroInterval = All(Imp(supported, Imp(zero, Imp(Le(Num(4), n), interval(boxed)))),
            ("U", "UnboxedCommonFlow"), ("mu", "DepthPMF"), ("n", "Nat"));
        Formula delta = F.Id("delta");
        Formula meanRepair(Formula f) => Equal(Call("meanCoordinate", f, n),
            Add(Times(Fraction(Num(4), Num(9)), Pow(Fraction(Num(2), Num(9)), n)), delta));
        Formula floor = And(Le(Times(Fraction(Times(Fraction(Num(4), Num(9)), rho),
            Fraction(Num(9839648), Num(2657205))), Pow(Fraction(Num(2), Num(9)), n)), delta),
            Seq(Num(0), Lt, delta));
        Formula midRepair = All(Imp(midpoint, Imp(Le(Num(5), n), Imp(meanRepair(flow), floor))),
            ("F", "CommonFlow"), ("n", "Nat"), ("delta", "Real"));
        Formula zeroRepair = All(Imp(supported, Imp(zero, Imp(Le(Num(5), n), Imp(meanRepair(boxed), floor)))),
            ("U", "UnboxedCommonFlow"), ("mu", "DepthPMF"), ("n", "Nat"), ("delta", "Real"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original supported risk, zero face and necessary repairs.", H("Original supported risk, zero face and necessary repairs"), Blocks(
                Paragraph(Text("DepthPMF is any probability mass function on positive natural depths; the two positivity predicates mean mu(1)!=0 and mu(2)!=0. Exactly the original DepthLaw.rate(k) targets are retained. supportedRisk(nu,mu) is max over p,beta of the real supremum over every k with mu(k)!=0 of the complete-configuration mean TV to native(s,rate(k)), minus radius(s). radius(p)=1116529/22781250 and radius(beta)=239/6750. Every target loss is measurable and lies in [0,1], so the real supported supremum is bounded; supported endpoints make it nonempty. rate(1)=1/3 and rate(2)=2/5 are exact Fibonacci evaluations.")),
                Paragraph(Text("PhaseMargins means a phase-indexed family of measures on RegularDescriptor(s); probabilityMargins requires probability at both phases. UnboxedCommonFlow carries exactly the original CommonFlow law, joint-flow, disintegration, unweighted margin and full normalized-residual fields, omitting only boxP and boxB. unboxedMargins and flowMargins select those same original margins. zeroFace(U,mu) fills only the two proved box fields after zero risk; it retains U's actual laws, kernels, joint flows and all marginal and residual equations.")),
                Paragraph(Text("The coordinate triangle slack is |D{t}-P_a{t}|+|D{t}-P_b{t}|-|P_a{t}-P_b{t}|. Singleton removal or insertion in the complete endpoint sign event bounds it by twice the full TV triangle slack. At zero supported risk, endpoint budgets force the nonnegative integrated TV slack, hence each coordinate slack, to vanish. Countability synchronizes every coordinate, including infinity, and equality in the real absolute-value triangle yields EndpointBox. This argument assumes no boxes at its input.")),
                Paragraph(Text("pEventMean(F)=integral Q(Ep).toReal dnuP; pMeanLoss is integral fullLoss(p,b) dnuP. The boxed p midpoint is the separate value 11758471/22781250. It imposes neither a suspended midpoint nor all-supported budgets. For a proposed repair delta is the difference of its corrected meanCoordinate from (4/9)(2/9)^n. The two NULL155 p laws have this common native lower tail for n>=5; the repair theorem is a necessary condition on a single actually compatible repaired pair, not on its retained finite features.")),
                Node("original-supported-risk-normalized", "original_risk_normalized", "The unchanged all-supported risk bound", risk,
                    "The opposite endpoint remains one original supported target in the full supremum. Complete configuration TV triangle and integration give radius(p)<=J+completeLoss. Apply normalized_stability for both endpoints and all n>=4."),
                Node("unboxed-zero-face-boxes", "zero_face_boxes", "Zero supported excess proves full boxes", boxes,
                    "The nonnegative coordinate slack has zero integral at every complete atom under the original arbitrary Borel probability margin. AE zero and countability yield all full endpoint intervals. Neither normalized residuals nor preassumed boxes are used in this implication."),
                Node("separate-boxed-p-midpoint", "boxed_p_midpoint", "Each p endpoint loss at the separate midpoint", midpointLoss,
                    "The full Ep TV formula integrates to radius(p) at each endpoint. No suspended midpoint or supported nonendpoint budget is inferred."),
                Node("boxed-midpoint-mean-interval", "midpoint_mean_interval", "Both mean bounds at the separate midpoint", midInterval,
                    "Each p endpoint mean loss lower-bounds completeLoss by radius(p). Normalize the two stability estimates and substitute the two slack definitions on the same meanCoordinate."),
                Node("unboxed-zero-face-mean-interval", "zero_face_mean_interval", "Both mean bounds from unboxed zero risk", zeroInterval,
                    "zeroFace constructs the boxed CommonFlow from the same unboxed pair. The original risk triangle at J=0 gives the loss lower bound, and normalized stability yields the simultaneous interval for its unchanged coordinate mean."),
                Node("boxed-midpoint-repair-floor", "midpoint_repair_floor", "Necessary repair on the separate midpoint face", midRepair,
                    "The corrected mean equation identifies delta with the lower signed slack. The lower normalized correction implies the decaying positive floor for every n>=5."),
                Node("unboxed-zero-face-repair-floor", "zero_face_repair_floor", "Necessary repair on the original zero-risk face", zeroRepair,
                    "The zero-face construction preserves the original pair. Its lower correction gives the same decaying positive floor, even when the proposed repaired pair varies with the return index."),
                Paragraph(Text("These bounds construct no feasible or operational pair and determine no general positive risk gap. They supply no finite representation, exact sampler, installed source-independent program or paid acquisition. The original common depth, both accepted seeds, every paid rejection, partial parse and return, complete record including noncompletion, identical acquired and synthetic updates, matching Stop and all COMPLETE charges retain their source meaning. No additional observation port, reset or source-depth draw is introduced.")))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Times(Formula a, Formula b) => Multiply(Grp(a), Grp(b));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Ae(Formula mu, Formula x, Formula body) => Call("AE", mu, x, body);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
}
