using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class NoncompactStrassenDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Law => Call("ProbabilityMeasure", Real);
    private static Formula Joint => Call("ProbabilityMeasure", Seq(Real, Times, Real));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("mu", Law), All("nu", Law), Call("IntegrableIdentity", V("mu")),
            Sp, Rightarrow, Call("IntegrableIdentity", V("nu")), Sp, Rightarrow),
        Seq(Open, Call("Mean", V("mu")), Eq, Call("Mean", V("nu")), Sp, Land),
        Seq(All("phi", Seq(Real, To, Real)), Call("ConvexOn", Real, Call("univ"), V("phi")),
            Sp, Rightarrow, Call("IntegrableAbs", V("phi"), V("mu")), Sp, Rightarrow,
            Call("IntegrableAbs", V("phi"), V("nu")), Sp, Rightarrow,
            Call("Integral", V("phi"), V("mu")), Sp, Leq, Sp,
            Call("Integral", V("phi"), V("nu")), Close),
        Seq(Iff, Sp, Exists, Sp, V("pi"), Colon, Sp, Joint, Comma, Sp,
            Call("Pushforward", V("pi"), Call("fst")), Eq, V("mu"), Sp, Land),
        Seq(Call("Pushforward", V("pi"), Call("snd")), Eq, V("nu"), Sp, Land,
            Call("NativeConditionalMean", V("pi")))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For arbitrary real Borel probability laws with finite first moments, convex order is equivalent to one actual martingale coupling with exact marginals and native joint conditional expectation.",
        H("Scalar Strassen equivalence with finite first moments"),
        Blocks(
            Describe.Lean(DescribeId.Create("noncompact-scalar-strassen"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NoncompactStrassen.strassen_iff"),
                H("Global convex tests and one native martingale joint"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/leskela2017conditionalconvex")),
                Blocks(
                    Paragraph(Text("All laws are Borel probability measures. IntegrableIdentity(rho) means that x maps to x is integrable against the underlying measure of rho. Mean is that identity integral. Integral(phi,rho) is the real Bochner integral; IntegrableAbs(phi,rho) means integrability of x maps to |phi(x)|. The test phi is globally real-valued and convex on all of the real line. It is quantified only when its absolute value is integrable under both mu and nu.")),
                    Paragraph(Text("Pushforward(pi,fst)=mu and Pushforward(pi,snd)=nu are equalities of the underlying pushforward measures, not approximate marginal constraints. NativeConditionalMean(pi) means pi.toMeasure[Prod.snd | (borel R).comap Prod.fst] equals Prod.fst almost everywhere under pi.toMeasure. The existential quantifier chooses one real-plane probability joint before this conditional expectation is asserted. There is no support, finite-support, density, nonatomicity or supplied-coupling premise. The conclusion asserts neither uniqueness nor an algorithm, vector or process extension.")),
                    Paragraph(Text("For existence, integrable hinge tests give stop-loss order. Synchronized equal-quantile-bin means preserve both original means and finite convex order. The finite majorization supplier constructs actual martingale joint laws with these exact finite marginals. Their marginals converge weakly and have genuine uniform absolute-first-moment tails. Tightness of the two marginal ranges implies tightness of the joint range. Prokhorov compactness chooses one subsequence and one joint limit, whose two exact marginals follow from continuity of pushforwards.")),
                    Paragraph(Text("The exact limiting marginals transfer coordinate integrability to that same joint. The first-moment weak-limit theorem passes every bounded continuous displacement integral to it, using clipping of the integrand and the actual uniform coordinate tails. The shared finite weighted-measure argument extends zero tests to bounded Borel functions, and the original conditional-expectation bridge gives the native joint-a.e. martingale identity. No re-extraction depends on the test function.")),
                    Paragraph(Text("Conversely, the native conditional mean and the conditional-expectation integral identity give equal means. Global real convexity implies continuity. Transfer the given absolute test integrability through each exact marginal, apply conditional Jensen to the second coordinate, replace its conditional mean by the first coordinate, and integrate. This yields precisely the stated common-integrability convex-test order. The result is the scalar finite-first-moment Strassen theorem; no literature originality is claimed."))),
                DescribeRole.Theorem))));
}
