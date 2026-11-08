using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalActionDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => Seq(Id(s), Open,
        new Formula.LatexSequence([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula St(params Formula[] xs) => Disp(new Formula.Aligned([.. xs]));
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), InMacro, Sp, t, Comma, Sp);
    private static Formula RR => Seq(Mathbb, Grp(Id("R")));
    private static Formula ZZ => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Act(Formula c, Formula u) => Call("action", c, u);
    private static DocumentBlock.Describe Desc(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("rational-action-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalAction." + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive rational interval homeomorphisms give the exact north-south map and all its integer iterates.",
        H("Rational Closed Interval Action"), Blocks(
        Paragraph(Text("Let I=[0,1]. For a positive real parameter c define action(c,u)=cu/(1-u+cu), and let H(c) denote this map as a homeomorphism of I. "
            + "The denominator is positive even at both endpoints; the inverse is action(1/c,u). The map f is H(2), exactly the rationalIntervalMap used in the marker classification. "
            + "The parameter is multiplicative; no real exponential or logarithmic parametrization is required.")),
        Desc("denominator_pos", "Positive denominator on the closed interval",
            St(Seq(All("c", RR), All("u", Id("I")), D(0), Lt, Id("c"), Rightarrow, Sp,
                D(0), Lt, D(1), Minus, Id("u"), Plus, Id("c"), Id("u"))),
            "For u<1 the term 1-u is positive and cu is nonnegative. At u=1 the denominator is c>0."),
        Desc("continuous_action", "Joint continuity on positive parameters and the closed interval",
            St(Seq(Operatorname, Grp(Id("Continuous")), Open,
                Open, Id("c"), Comma, Id("u"), Close, InMacro, Sp,
                Open, D(0), Comma, Infty, Close, Times, Sp, Id("I"), Mapsto, Sp, Act(Id("c"), Id("u")), Close)),
            "The positive denominator permits division of continuous coordinate functions on the full parameter product."),
        Desc("action_mul", "Multiplicative action law",
            St(Seq(All("c", RR), All("d", RR), All("u", Id("I")), D(0), Lt, Id("c"), Land, Sp, D(0), Lt, Id("d"), Rightarrow, Sp,
                Act(Id("c"), Act(Id("d"), Id("u"))), Eq, Act(Seq(Id("c"), Id("d")), Id("u")))),
            "Clearing the positive denominators gives the action law. The unit parameter acts identically and the reciprocal parameter gives both inverse identities."),
        Desc("homeomorph_zpow", "All integer powers are rational actions",
            St(Seq(All("c", RR), All("k", ZZ), D(0), Lt, Id("c"), Rightarrow, Sp,
                Pow(Call("H", Id("c")), Id("k")), Eq, Call("H", Pow(Id("c"), Id("k"))))),
            "Positive and negative integer induction uses the multiplication law in the homeomorphism group. In particular f to the integer power k is H(2 to the power k)."),
        Desc("closedPseudoOrbit_iff", "The literal closed pseudo-orbit domain",
            St(Seq(All("delta", RR), Forall, Sp, Id("x"), Colon, ZZ, To, Sp, Id("I"), Comma, Sp,
                Call("ClosedPseudoOrbit", Id("f"), Id("delta"), Id("x")), Leftrightarrow, Sp,
                Call("ClosedRationalPseudoOrbit", Id("delta"), Id("x")))),
            "The left side is the existing compact-selector predicate dist(x(k+1),f(x(k)))<=delta at every integer k. The right side is the absolute-error predicate for 2u/(1+u). "
                + "Symmetry of real distance identifies them, including equality in the error bound and both interval endpoints."),
        Desc("orbit_neg_tendsto", "Negative orbit limit",
            St(Seq(All("u", Id("I")), Id("u"), Lt, D(1), Rightarrow, Sp,
                Lim, Underscore, Grp(Id("n"), To, Sp, Infty), Pow(Id("f"), Seq(Minus, Id("n"))), Open, Id("u"), Close, Eq, D(0))),
            "The index n ranges over natural numbers. Substituting c=(1/2)^n into the rational formula gives a numerator tending to zero and a denominator tending to 1-u>0."),
        Desc("orbit_pos_tendsto", "Positive orbit limit",
            St(Seq(All("u", Id("I")), D(0), Lt, Id("u"), Rightarrow, Sp,
                Lim, Underscore, Grp(Id("n"), To, Sp, Infty), Pow(Id("f"), Id("n")), Open, Id("u"), Close, Eq, D(1))),
            "The index n ranges over natural numbers. Dividing numerator and denominator by 2^n gives u/((1-u)(1/2)^n+u), whose limit is one. The two endpoints are fixed by every action parameter.")
        )));
}
