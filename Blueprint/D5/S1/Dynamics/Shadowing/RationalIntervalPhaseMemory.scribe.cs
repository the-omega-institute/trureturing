using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalPhaseMemoryDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => Seq(Id(s), Open,
        new Formula.LatexSequence([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Fr(Formula n, int d) => Seq(Frac, Grp(n), Grp(Num(d)));
    private static Formula St(params Formula[] xs) => Disp(new Formula.Aligned([.. xs]));
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), InMacro, Sp, t, Comma, Sp);
    private static Formula RR => Seq(Mathbb, Grp(Id("R")));
    private static Formula ZZ => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Pg(Formula g) => Seq(Id("P"), Underscore, Grp(g));
    private static Formula Act(Formula c, Formula u) => Call("action", c, u);
    private static Formula Iter(Formula u) => Seq(Pow(Id("f"), Id("k")), Open, u, Close);
    private static Formula Tx => Call("T", Id("x"));
    private static Formula Rx => Call("R", Id("x"));
    private static Formula Ex => Call("e", Id("x"));
    private static Formula Shift => Call("shift", Id("k"), Id("x"));
    private static Formula Defect => Call("d", Iter(Tx), Call("T", Shift));
    private static Formula Error => Call("d", Iter(Tx), Call("x", Id("k")));
    private static Formula PseudoMap => Seq(Call("Continuous", Id("T")), Land, Sp,
        Open, All("p", Id("I")), Call("T", Call("O", Id("p"))), Eq, Id("p"), Close, Land, Sp);
    private static Formula Tail => Seq(Lim, Underscore, Grp(Bar, Id("k"), Bar, To, Sp, Infty));
    private static DocumentBlock.Describe Desc(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("rational-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory." + name), H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/artigue2025shadowing")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one fixed phase-memory perturbation of the explicit interval orbit retraction satisfies the original shadowing and L-shadowing definitions.",
        H("Rational Interval Phase Memory"), Blocks(
        Paragraph(Text("Let I=[0,1], f(u)=2u/(1+u), delta=1/256, and P=P_delta, where P_gamma is the entire closed domain of sequences x:Z->I with d(x(k+1),f(x(k)))<=gamma at every integer k. "
            + "Use the product subtype topology and the completed finite-marker orbit retraction R. Set e(x)=d(x(0),f(x(-1))) and T(x)=action(1+e(x),R(x)), with action(c,u)=cu/(1-u+cu). "
            + "This is one fixed map on P; neither its formula nor its memory coordinate depends on an accuracy, time or restriction radius. For x in a smaller P_gamma, T and R mean evaluation after literal inclusion into P. "
            + "Write shift(k,x)(j)=x(k+j), O(p)(j)=f^j(p), and d for the inherited interval distance. Artigue supplies the definitions; the rational phase-memory construction is separate from the cited paper.")),
        Desc("action_commutes", "Commutation at all integer times",
            St(Seq(All("c", RR), All("k", ZZ), All("u", Id("I")), D(0), Lt, Id("c"), Rightarrow, Sp,
                Iter(Act(Id("c"), Id("u"))), Eq, Act(Id("c"), Iter(Id("u"))))),
            "The existing action multiplication law and f^k=H(2^k) give commutation, for negative times as well as positive times."),
        Desc("action_displacement", "Exact phase displacement",
            St(Seq(All("e", RR), All("u", Id("I")), D(0), Le, Sp, Id("e"), Rightarrow, Sp,
                Act(Seq(D(1), Plus, Id("e")), Id("u")), Minus, Id("u"), Eq,
                Frac, Grp(Id("e"), Id("u"), Open, D(1), Minus, Id("u"), Close),
                Grp(D(1), Plus, Id("e"), Id("u")))),
            "Clear the positive denominator 1+eu. The displacement is nonnegative on the full closed interval."),
        Desc("action_displacement_le", "Quarter-error bound",
            St(Seq(All("e", RR), All("u", Id("I")), D(0), Le, Sp, Id("e"), Rightarrow, Sp,
                Call("d", Act(Seq(D(1), Plus, Id("e")), Id("u")), Id("u")), Le, Sp, Fr(Id("e"), 4))),
            "The exact displacement, u(1-u)<=1/4 and 1+eu>=1 give a bound including u=0 and u=1."),
        Desc("continuous_T", "Continuity on the unchanged full domain",
            St(Seq(Operatorname, Grp(Id("Continuous")), Open, Id("T"), Colon, Id("P"), To, Sp, Id("I"), Close)),
            "The actual link error at minus one is continuous. Combine it with continuity of R and the existing joint continuity of the positive rational action."),
        Desc("T_trueOrbit", "All genuine orbits are fixed",
            St(Seq(All("p", Id("I")), Call("T", Call("O", Id("p"))), Eq, Id("p"))),
            "The origin memory of every true orbit is zero, so action(1,R(O(p)))=p. This includes both endpoint orbits."),
        Desc("T_iterate", "The original memory parameter persists under iteration",
            St(Seq(All("x", Id("P")), All("k", ZZ), Iter(Tx), Eq,
                Act(Seq(D(1), Plus, Ex), Iter(Rx)))),
            "Commutation keeps e(x) fixed while f^k acts on R(x). It does not replace that parameter with the shifted memory."),
        Desc("T_shadowing_defect", "Actual uniform phase defect",
            St(Seq(All("gamma", RR), Id("gamma"), Le, Sp, Fr(D(1), 256), Rightarrow, Sp,
                All("x", Pg(Id("gamma"))), All("k", ZZ), Defect, Le, Sp, Fr(Id("gamma"), 2))),
            "Exact equivariance gives R(shift(k,x))=f^k(R(x)). Apply the quarter-error estimate to e(x) and e(shift(k,x)), each bounded by gamma, and use the triangle inequality."),
        Desc("T_shadowing_map", "Literal shadowing-map condition",
            St(PseudoMap, Seq(Forall, Sp, Varepsilon, Gt, D(0), Comma, Sp,
                Exists, Sp, GammaLower, Gt, D(0), Comma, Sp, GammaLower, Le, Sp, Fr(D(1), 256), Land, Sp,
                All("x", Pg(GammaLower)), All("k", ZZ), Defect, Le, Sp, Varepsilon)),
            "Choose gamma=min(delta,2 epsilon). This is exactly Definition 3.1 for the prescribed single T, at every integer time."),
        Desc("T_global_shadowing", "Uniform global tracing",
            St(Seq(Forall, Sp, Varepsilon, Gt, D(0), Comma, Sp,
                Exists, Sp, GammaLower, Gt, D(0), Comma, Sp, GammaLower, Le, Sp, Fr(D(1), 256), Land, Sp,
                All("x", Pg(GammaLower)), All("k", ZZ), Error, Lt, Varepsilon)),
            "Take R's global tracing scale for epsilon/2 and shrink it to at most 2 epsilon. The additional displacement is at most gamma/4. No support condition on errors is imposed."),
        Desc("action_orbit_displacement_tendsto", "Both tails of every fixed phase perturbation",
            St(Seq(All("c", RR), All("p", Id("I")), D(0), Lt, Id("c"), Rightarrow, Sp,
                Tail, Call("d", Act(Id("c"), Iter(Id("p"))), Iter(Id("p"))), Eq, D(0))),
            "An interior orbit tends to zero at its negative tail and one at its positive tail. Continuity of action(c,.) and its two fixed endpoints make the displacement tend to zero at both tails. "
                + "Endpoint base points are handled identically zero. The two natural-number limits are joined into the cofinite limit on Z. No uniform rate over p or c is claimed."),
        Desc("T_limit_shadowing", "Full-domain two-sided limit tracing",
            St(Seq(All("x", Id("P")), Tail, Call("linkError", Id("x"), Id("k")), Eq, D(0), Rightarrow, Sp,
                Tail, Error, Eq, D(0))),
            "For the fixed x use p=R(x), c=1+e(x) in the phase limit. Commutation and the triangle inequality combine that limit with the completed full-domain limit theorem for R. "
                + "The domain contains arbitrary infinitely supported error sequences tending to zero in both directions."),
        Desc("T_L_shadowing_map", "Literal L-shadowing-map condition",
            St(PseudoMap, Seq(Forall, Sp, Varepsilon, Gt, D(0), Comma, Sp,
                Exists, Sp, GammaLower, Gt, D(0), Comma, Sp, GammaLower, Le, Sp, Fr(D(1), 256), Land, Sp,
                All("x", Pg(GammaLower)), Tail, Call("linkError", Id("x"), Id("k")), Eq, D(0), Rightarrow),
                Seq(Open, All("k", ZZ), Error, Lt, Varepsilon, Close, Land, Sp, Tail, Error, Eq, D(0))),
            "The global tracing scale works simultaneously for the uniform all-time bound and the cofinite limit, with the same output T(x). This is Definition 4.5, including all admitted two-sided limit pseudo-orbits. "
                + "The literal weighted-sum self-tuning antecedent and the every-positive-radius counterwitnesses are further obligations, not conclusions of this module.")
        )));
}
