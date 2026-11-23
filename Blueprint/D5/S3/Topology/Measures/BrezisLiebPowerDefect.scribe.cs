using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class BrezisLiebPowerDefectDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Lam(string name, Formula body) =>
        Seq(Open, V(name), Sp, Mapsto, Sp, body, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Pow(Formula a) => Seq(a, Caret, Grp(V("p")));
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Vert, Sp);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Fn => At(V("f"), V("n"));
    private static Formula Rn => At(V("r"), V("n"));
    private static Formula Dn => At(V("d"), V("n"));
    private static Formula Mass(Formula h) => Call("A", h);
    private static Formula Energy(Formula h) => Call("E", h);
    private static Formula Integrable(Formula h) => Call("Integrable", h, V("mu"));
    private static Formula PowerFn(Formula h) => Lam("x", Pow(Norm(At(h, V("x")))));
    private static Formula Tendsto(Formula h, Formula value) =>
        Call("Tendsto", h, V("atTop"), Call("nhds", value));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("Omega", Seq(V("Type"), Underscore, Grp(V("u")))),
            OpenBracket, Call("MeasurableSpace", V("Omega")), CloseBracket),
        Seq(All("mu", Call("Measure", V("Omega"))), All("p", V("Real")),
            D(0), Sp, F.Lt, Sp, V("p"), Sp, Rightarrow),
        Seq(All("M", V("NNReal")),
            All("f", Arrow(V("Nat"), Arrow(V("Omega"), V("Complex")))),
            All("g", Arrow(V("Omega"), V("Complex")))),
        Seq(Open, All("n", V("Nat")), Call("AEStronglyMeasurable", Fn, V("mu")),
            Close, Sp, Rightarrow),
        Seq(Call("AE", V("mu"), Lam("x", Tendsto(
            Lam("n", At(Fn, V("x"))), At(V("g"), V("x"))))), Sp, Rightarrow),
        Seq(Open, All("n", V("Nat")), Le(Mass(Fn), Call("ofNNReal", V("M"))),
            Close, Sp, Rightarrow),
        Call("AEStronglyMeasurable", V("g"), V("mu")),
        Seq(Land, Sp, Le(Mass(V("g")), Call("ofNNReal", V("M")))),
        Seq(Land, Sp, Integrable(PowerFn(V("g")))),
        Seq(Land, Sp, Open, All("n", V("Nat")),
            Integrable(PowerFn(Fn)), Sp, Land, Sp, Integrable(PowerFn(Rn)),
            Sp, Land, Sp, Integrable(Dn), Close),
        Seq(Land, Sp, Tendsto(Lam("n", Call("integral", V("mu"),
            Lam("x", Abs(At(Dn, V("x")))))), D(0))),
        Seq(Land, Sp, Tendsto(Lam("n", Sub(Energy(Fn), Energy(Rn))), Energy(V("g"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full L1 power splitting for complex functions on an arbitrary measure space.",
        H("Brézis–Lieb power defect"),
        Blocks(
            Paragraph(Text("The universe u, measurable space Omega and measure mu are arbitrary. "
                + "Real powers are taken of nonnegative norms. Write r(n)(x) = f(n)(x) - g(x), "
                + "d(n)(x) = norm(f(n)(x))^p - norm(r(n)(x))^p - norm(g(x))^p, "
                + "A(h) = lintegral mu (x maps to enorm(h(x))^p), and "
                + "E(h) = integral mu (x maps to norm(h(x))^p). "
                + "The coercion ofNNReal sends the finite nonnegative bound M into ENNReal. "
                + "AE(mu,P) means that P holds mu-almost everywhere; Integrable is real Bochner integrability.")),
            Describe.Lean(DescribeId.Create("brezis-lieb-power-defect"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/BrezisLiebPowerDefect.brezis_lieb_power_defect"),
                H("Full absolute defect and signed energy splitting"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/brezislieb1983pointwise")),
                Blocks(
                    Paragraph(Text("The assumptions are almost-everywhere strong measurability of every f(n), "
                        + "almost-everywhere convergence of the whole sequence to g, and the common finite positive-power mass bound. "
                        + "The conclusions include measurability and the same mass bound for g, integrability of its power, "
                        + "integrability of each original power, residual power and real defect, convergence to zero of the integral "
                        + "of the absolute defect, and the signed difference of the two energies tending to the energy of g.")),
                    Paragraph(Text("Fatou's lemma gives the limit mass bound. The Lp algebra gives integrability of the residual powers, "
                        + "also when 0 < p < 1. The scalar estimate below separates a small multiple of the original power "
                        + "from an integrable multiple of the limit power. For fixed positive epsilon, "
                        + "F(n)(x) = max(abs(d(n)(x)) - epsilon norm(f(n)(x))^p, 0) is bounded by "
                        + "(C + 1) norm(g(x))^p and tends almost everywhere to zero. Dominated convergence applies to F. "
                        + "The integral of abs(d(n)) is at most epsilon M plus the integral of F(n). "
                        + "Letting epsilon decrease to zero gives the full L1 conclusion. "
                        + "The integral norm inequality and the explicit integrability statements then give signed splitting.")),
                    Paragraph(Text("For every p > 0 and epsilon > 0 there is a nonnegative real C such that, for all complex a and b, "
                        + "abs(norm(a+b)^p - norm(a)^p) <= epsilon norm(a)^p + C norm(b)^p. "
                        + "Continuity of the power at one handles b small relative to a; the complementary case bounds a by a multiple of b. "
                        + "This is the power estimate used in the proof, with no differentiability or convexity assumption.")),
                    Paragraph(Text("There is no finiteness, sigma-finiteness, semifiniteness or completeness assumption on mu. "
                        + "No common dominator, uniform integrability, tightness, weak convergence, subsequence or convergence "
                        + "of the individual energies is assumed. Empty spaces, zero measures, M = 0, g = 0, p = 1, "
                        + "fractional p below one, noninteger p above one and arbitrary complex phases are included.")),
                    Paragraph(Text("A nonzero example on the natural numbers with counting measure is "
                        + "g(k) = i at k = 0 and zero elsewhere, while f(n)(k) = i at k = 0 or k = n+1 and zero elsewhere. "
                        + "For every p > 0, the original power mass is two, the limit power mass is one, "
                        + "and the residual pulse has power mass one. The defect is identically zero. "
                        + "The moving residual does not tend to zero in power mass, and the original sequence has no common integrable "
                        + "power dominator. Splitting therefore does not assert strong Lp convergence of the original sequence.")),
                    Paragraph(Text("The strong L1 statement is the power specialization of Theorem 2, Remark (ii) and Example (a) "
                        + "in Brézis and Lieb's 1983 paper. Theorem 1 separately states signed splitting. "
                        + "The application after (2.25) in arXiv:2611.26428v1 combines signed nonlinear splitting with separate "
                        + "kinetic estimates and nonvanishing information; the power theorem alone supplies neither of those inputs."))),
                DescribeRole.Theorem))));
}
