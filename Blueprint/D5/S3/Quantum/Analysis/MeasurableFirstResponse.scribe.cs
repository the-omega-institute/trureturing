using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class MeasurableFirstResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original vectorwise measurable evolution has an actual Bochner first response, sharp local exponential remainder and signed derivative uniform on the closed time triangle.",
        H("Sharp first response of the original measurable evolution"), Blocks(
            Paragraph(Text("Let E be a complex Banach space in any universe, including the trivial space. S is the original NonautonomousDysonPhillips.Contraction E: a strongly continuous contraction semigroup on nonnegative real times with identity at zero. Fix a real T>=0. For each real s, B(s) and H(s) are bounded complex-linear endomorphisms of E. For each fixed vector z separately, s maps to B(s)z and to H(s)z are AE strongly measurable for real Lebesgue measure restricted to Icc(0,T). The scalar functions g,h are nonnegative and integrable on this interval and dominate the operator norms pointwise there.")),
            Paragraph(Text("Write U_Q(t,r)=MeasurableNonautonomousDysonPhillips.measurableEvolution(S,Q,t,r), the SAME native realization of the original ordered vector Bochner series. Write G_k(r,t)=the actual interval integral of k from r to t. Define V(B,H,t,r,x)=response(S,B,H,t,r,x) as the actual interval Bochner integral from r to t of U_B(t,s)H(s)U_B(s,r)x with respect to real Lebesgue measure. These definitions introduce neither a new evolution nor an assumed response formula.")),
            Describe.Lean(DescribeId.Create("native-sharp-response-and-uniform-signed-derivative"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/MeasurableFirstResponse.uniform_signed_response"),
                H("Actual first response, sharp second-order defect and uniform signed derivative"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every 0<=r<=t<=T and every x, the displayed response integrand is IntervalIntegrable for volume. The norm bound uses the local clock G_g(r,t), and the defect is bounded by exp(G_g)(exp(G_h)-1-G_h), then by one half times exp(G_g+G_h)G_h squared, with norm(x) in both bounds. The second conjunct has one delta>0 for each x and eta>0; it works for every signed nonzero epsilon of smaller absolute value and simultaneously for all r,t in the whole closed triangle.")),
                    Paragraph(Text("Actual B/B integrability comes from native strong vector continuity, evaluation_integrable applied to H(s)U_B(s,r)x, and the original forced_regular theorem. It is established independently of the two mixed Duhamel integrabilities. For the response norm, use the native local exponential bounds on both sides of H(s), the scalar h domination, Bochner norm comparison and adjacent-clock additivity. The two g clocks combine exactly to G_g(r,t).")),
                    Paragraph(Text("For a nonnegative integrable scalar h on Icc(r,t), the suffix clock K(s)=integral from s to t of h is absolutely continuous. Its range is contained in Icc(0,G_h(r,t)). Exponential is Lipschitz on this compact range, so exp(K(s)) is absolutely continuous. The AE derivative chain rule and the absolutely continuous fundamental theorem give the exact identity integral from r to t of h(s)exp(K(s))=exp(G_h(r,t))-1. The proof includes r=t and zero control mass and never divides by that mass.")),
                    Paragraph(Text("The sharp native increment comparison is norm(U_(B+H)(t,r)x-U_B(t,r)x)<=exp(G_g(r,t))(exp(G_h(r,t))-1)norm(x). Use the RIGHT mixed Duhamel identity, whose factors are U_(B+H)(t,s), H(s), U_B(s,r). Its native local bounds combine to exp(G_g(r,t)) times h(s)exp(G_h(s,t)); the exact suffix-clock integral proves the comparison. This uses the actual perturbed native evolution, without substituting the free S.action kernel for a relative evolution.")),
                    Paragraph(Text("Subtract the actual B/B response from the same right Duhamel integral. Bochner linearity yields the integrand (U_(B+H)(t,s)-U_B(t,s))H(s)U_B(s,r)x. Apply the increment comparison on Icc(s,t) to that actual vector. The background clocks again add, and the remaining scalar integral is integral of h(s)(exp(G_h(s,t))-1)=exp(G_h(r,t))-1-G_h(r,t). The increment comparison therefore bounds the norm of the second-order defect integrand by exp(G_g(r,t))h(s)(exp(G_h(s,t))-1)norm(x). Taylor's theorem with the Lagrange remainder, applied to the real exponential to order one, gives exp(b)-1-b<=exp(b)b squared/2 for b>=0.")),
                    Paragraph(Text("For real epsilon, epsilon times H has pointwise scalar control abs(epsilon)h and the same required evaluation measurability. The response is real homogeneous by bounded linearity and Bochner scalar linearity. For nonzero epsilon the scaled defect is exactly epsilon inverse acting on the second-order defect. If abs(epsilon)<=1, horizon-clock monotonicity gives a uniform quotient-error bound abs(epsilon)C, where C=exp(G_g(0,T)+G_h(0,T))G_h(0,T) squared norm(x)/2. The proof chooses delta=min(1,eta/(C+1)), which stays positive when the horizon, controls or vector vanish. No positivity of C is needed.")),
                    Paragraph(Text("All universes, trivial E, zero horizon, zero controls, x=0 and diagonal times are in scope. Coefficients may fail to commute at every stage, and their displayed order is preserved. No finite dimensionality, separability, operator-norm measurability, continuity or integrability, common exceptional set over uncountably many vectors, generator-domain premise, extra joint measurability or interval-exterior regularity is assumed. The conclusion is a vector response and quantitative uniform remainder; it asserts no Frechet-analytic map on an L1 operator space, numerical algorithm, complexity or physical law.")),
                    Paragraph(Text("The mechanism is classical variation of constants and first-order exponential Taylor control. Native evolutions and both actual-integrable Duhamel identities are reused from MeasurableNonautonomousDysonPhillips and MeasurableRelativeDuhamel; Mathlib supplies Bochner comparisons and linearity, absolute continuity, AE FTC, exponential differentiability and Taylor's theorem. The bounded autonomous Dyson-Phillips provenance is documented in Library/Topology/engelnagel2000boundedperturbation.md and the original native development. This is a formal derivation for the stated weak evaluation-measurability hypotheses, without a literature-novelty claim."))), DescribeRole.Theorem))));

    private static Formula R => Call("Real");
    private static Formula E => X("E");
    private static Formula Z => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula X(string n) => F.Id(n);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(X(n), Colon, d), Mapsto, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Clm => Call("ComplexCLM", E, E);
    private static Formula Coeff => Arrow(R, Clm);
    private static Formula J => Call("Icc", Z, X("T"));
    private static Formula Mu => Call("restrict", Call("volume"), J);
    private static Formula Meas(Formula q) => All("z", E, Call("AEStronglyMeasurable", Lam("s", R, At(At(q, X("s")), X("z"))), Mu));
    private static Formula Nonneg(Formula k) => All("s", R, Imp(Call("Mem", X("s"), J), Le(Z, At(k, X("s")))));
    private static Formula Bound(Formula q, Formula k) => All("s", R, Imp(Call("Mem", X("s"), J), Le(Norm(At(q, X("s"))), At(k, X("s")))));
    private static Formula U(Formula q, Formula t, Formula r, Formula x) => Call("measurableEvolution", X("S"), q, t, r, x);
    private static Formula V() => Call("response", X("S"), X("B"), X("H"), X("t"), X("r"), X("x"));
    private static Formula Integrand() => Lam("s", R, U(X("B"), X("t"), X("s"), At(At(X("H"), X("s")), U(X("B"), X("s"), X("r"), X("x")))));
    private static Formula Clock(Formula k) => Call("intervalIntegral", Call("volume"), X("r"), X("t"), k);
    private static Formula Exp(Formula v) => Call("exp", v);
    private static Formula Times(params Formula[] xs) => xs.Aggregate((a, b) => Multiply(a, b));
    private static Formula Triangle(Formula body) => All("r", R, All("t", R, Imp(Le(Z, X("r")), Imp(Le(X("r"), X("t")), Imp(Le(X("t"), X("T")), body)))));
    private static Formula Statement()
    {
        Formula b = X("B"), h = X("H"), g = X("g"), k = X("h"), x = X("x");
        Formula a = Clock(g), c = Clock(k);
        Formula diff(Formula q) => Subtract(U(q, X("t"), X("r"), x), U(b, X("t"), X("r"), x));
        Formula tail = Times(Exp(a), Subtract(Subtract(Exp(c), One), c), Norm(x));
        Formula quadratic = Times(new Formula.Fraction(One, new Formula.Number(2)), Exp(Add(a, c)), new Formula.Power(c, new Formula.Number(2)), Norm(x));
        Formula pointwise = Triangle(All("x", E, And(Call("IntervalIntegrable", Integrand(), Call("volume"), X("r"), X("t")),
            And(Le(Norm(V()), Times(Exp(a), c, Norm(x))), And(Le(Norm(Subtract(diff(Add(b, h)), V())), tail), Le(tail, quadratic))))));
        Formula quotient = Subtract(Smul(Call("inv", X("epsilon")), diff(Add(b, Smul(X("epsilon"), h)))), V());
        Formula signed = All("x", E, All("eta", R, Imp(Lt(Z, X("eta")), Exists("delta", R, And(Lt(Z, X("delta")),
            All("epsilon", R, Imp(Lt(Z, Call("abs", X("epsilon"))), Imp(Lt(Call("abs", X("epsilon")), X("delta")), Triangle(Lt(Norm(quotient), X("eta")))))))))));
        Formula result = And(pointwise, signed);
        Formula premises = Imp(Meas(b), Imp(Meas(h), All("g", Arrow(R, R), All("h", Arrow(R, R),
            Imp(Call("IntegrableOn", g, J, Call("volume")), Imp(Call("IntegrableOn", k, J, Call("volume")),
            Imp(Nonneg(g), Imp(Nonneg(k), Imp(Bound(b, g), Imp(Bound(h, k), result))))))))));
        return All("u", Call("Universe"), All("E", Call("Type", X("u")),
            Seq(OpenBracket, Call("NormedAddCommGroup", E), CloseBracket, Sp,
                OpenBracket, Call("NormedSpace", Call("Complex"), E), CloseBracket, Sp,
                OpenBracket, Call("CompleteSpace", E), CloseBracket, Sp,
                All("S", Call("Contraction", E), All("B", Coeff, All("H", Coeff,
                    All("T", R, Imp(Le(Z, X("T")), premises))))))));
    }
}
