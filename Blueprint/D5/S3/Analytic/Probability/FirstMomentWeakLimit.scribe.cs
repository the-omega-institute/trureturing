using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class FirstMomentWeakLimitDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Joint => Call("ProbabilityMeasure", Seq(Real, Times, Real));
    private static Formula Law(Formula n) => Call("measure", n);
    private static Formula At(string n, string x) => Call("apply", V(n), V(x));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("piSeq", Fn(Nat, Joint)), All("pi", Joint),
            Call("Tendsto", V("piSeq"), Call("atTop"), Call("nhds", V("pi"))),
            Sp, Rightarrow),
        Seq(Open, All("n", Nat), Call("Integrable", Call("fst"), Law(At("piSeq", "n"))),
            Sp, Land, Sp, Call("Integrable", Call("snd"), Law(At("piSeq", "n"))), Close, Sp, Rightarrow),
        Seq(Call("Integrable", Call("fst"), Law(V("pi"))), Sp, Rightarrow,
            Call("Integrable", Call("snd"), Law(V("pi"))), Sp, Rightarrow),
        Seq(Open, All("epsilon", Real), D(0), Lt, V("epsilon"), Sp, Rightarrow,
            Exists, Sp, V("R"), Colon, Sp, Real, Comma, Sp, D(0), Lt, V("R"),
            Sp, Land, Sp, All("n", Nat),
            Call("Tail", D(1), V("R"), At("piSeq", "n")), Plus,
            Call("Tail", D(2), V("R"), At("piSeq", "n")), Lt, V("epsilon"), Close,
            Sp, Rightarrow),
        Seq(All("h", Fn(Real, Real)), Call("Continuous", V("h")), Sp, Rightarrow,
            Open, Exists, Sp, V("M"), Colon, Sp, Real, Comma, Sp, D(0), Sp, Leq, Sp, V("M"),
            Sp, Land, Sp, All("x", Real), Bar, At("h", "x"), Bar, Sp, Leq, Sp, V("M"), Close,
            Sp, Rightarrow),
        Call("Tendsto", Seq(V("n"), Sp, Mapsto, Sp,
                Call("DisplacementIntegral", V("h"), At("piSeq", "n"))),
            Call("atTop"), Call("nhds", Call("DisplacementIntegral", V("h"), V("pi"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform absolute first-moment tails permit displacement tests to pass to a weak limit of real-plane probability laws.",
        H("Displacement integrals and first-moment tails"),
        Blocks(
            Paragraph(Text("Every law is a Borel probability measure on the real plane. The notation measure(rho) denotes its underlying measure, piSeq(n) denotes the nth law, and Tail(i,R,rho) is the integral of the absolute ith coordinate over the set where that absolute coordinate exceeds R. DisplacementIntegral(h,rho) is the integral of (y-x)h(x) against rho. The limit and every member of the sequence have both coordinates integrable. No common compact support, density, finite support, prescribed marginals or coupling premise is required.")),
            Describe.Lean(DescribeId.Create("first-moment-weak-limit-displacement"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/FirstMomentWeakLimit.tendsto_integral_displacement"),
                H("Convergence for every bounded continuous first-coordinate test"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("Put c_R(t)=max(-R,min(R,t)). The bounded continuous test is (c_R(y)-c_R(x))h(x); the factor h uses the original first coordinate. Every probability law remains the same. For nonnegative R at most r, the absolute error of a coordinate clipped at r is bounded by its absolute value times the indicator that its absolute value exceeds R. Integration bounds the displacement-test error by the sum of the two coordinate tails times the bound on h.")),
                    Paragraph(Text("For the limit law, dominated convergence applies as the natural-number clipping radius grows: the integrable majorant is (|y|+|x|)M. Choose one sufficiently large radius for the uniform sequence error and the limit error. Weak convergence supplies convergence of the bounded continuous clipped integrals at that radius, and the triangle inequality yields convergence of the original integrals. This is the classical truncation method for uniform integrability; it is a mathematical application of that method, with no originality claim.")),
                    Paragraph(Text("In martingale transport this result preserves zero continuous displacement integrals for a previously extracted single weak limit. It supplies neither the construction of ordered finite approximations nor their uniform tails, tightness, subsequence extraction, marginal identification, or the passage from continuous tests to native conditional expectation. Those require separate results."))),
                DescribeRole.Theorem))));
}
