using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class UniformTracingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/UniformTracing.";
    private static Formula X => F.Id("X");
    private static Formula Y => F.Id("Y");
    private static Formula f => F.Id("f");
    private static Formula g => F.Id("g");
    private static Formula p => F.Id("p");
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Inst(string c, Formula x) => Seq(OpenBracket, Call(c, x), CloseBracket);
    private static Formula All(Formula x, Formula t) => Seq(Forall, Sp, x, Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Types(bool metricX = false) => Seq(All(X, F.Id("Type")), Sp,
        Inst(metricX ? "MetricSpace" : "UniformSpace", X), Comma, Sp,
        All(Y, F.Id("Type")), Sp, Inst("UniformSpace", Y), Comma);
    private static Formula Maps() => Seq(All(p, Map(Y, X)), Sp, All(g, Map(Y, Y)), Sp, All(f, Map(X, X)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-cover and uniform shadowing agree on compact uniform spaces; positive expansivity supplies exact-fibre relative tracing.",
        H("Uniform Shadowing and Prescribed Sources"), Blocks(
        Describe.Lean(DescribeId.Create("cover-uniform-shadowing"), DeclarationHandle.Create(Owner + "cover_shadowing_iff_uniform"),
            H("The actual cover contract"), StatementSource.FromAuthor(St(
                Seq(All(X, F.Id("Type")), Sp, Inst("UniformSpace", X), Sp, Inst("CompactSpace", X), Comma),
                All(f, Map(X, X)), Seq(Call("HasShadowing", f), Sp, Iff, Sp, Call("UniformHasShadowing", f)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "For every finite open cover C, coverPairs(C) relates two points lying in a single member. "
                + "The Lebesgue-number lemma makes this an entourage. Conversely, a symmetric square root H of an entourage E "
                + "gives open neighborhoods inside H-balls; compactness selects a finite cover whose pair relation is contained in E. "
                + "These two constructions translate all quantifiers of the current HasShadowing interface. Empty spaces and arbitrary self-maps are allowed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("source-relative-orbit-lifting"), DeclarationHandle.Create(Owner + "source_relative_iff_orbit_lifting"),
            H("SR is exactly OL plus upstairs shadowing"), StatementSource.FromAuthor(St(Types(), Maps(),
                Hyp(Call("UniformContinuous", p)), Hyp(Call("UniformHasShadowing", g)),
                Seq(Call("SourceRelativeTracing", p, g, f), Sp, Iff, Sp, Call("OrbitLifting", p, g, f)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "SR means: for each upstairs entourage E choose D upstairs and V downstairs, before every sequence a and every prescribed x. "
                + "A D-pseudo-orbit with (p(a(n)), f^n(x)) in V must have a tracer b with p(b)=x and (g^n(b),a(n)) in E at all n. "
                + "OL replaces the pseudo-orbit by the exact orbit of an arbitrary a, and chooses V before a,x. SR implies OL since exact orbit errors are diagonal. "
                + "For the reverse implication choose H with H composed with H contained in E, the OL observation, its uniform square root, and a smaller upstairs observation "
                + "whose p-image is inside that square root. Shadow upstairs first, then lift the already prescribed x by OL and compose the two observations. "
                + "No semiconjugacy or surjectivity is required for this equivalence; uniform continuity is an explicit premise."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("positive-expansivity-source-relative"), DeclarationHandle.Create(Owner + "positive_expansivity_source_relative"),
            H("Deriving prescribed-source tracing"), StatementSource.FromAuthor(St(Types(true),
                Seq(Grp(), Inst("CompactSpace", Y), Comma), Maps(), Hyp(Call("Continuous", p)),
                Hyp(Call("Semiconj", p, g, f)), Hyp(Call("HasShadowing", g)), Hyp(Call("PositivelyExpansive", f)),
                Call("SourceRelativeTracing", p, g, f))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Positive expansivity supplies c>0 such that forward c-close orbits agree, with n=0 included. "
                + "Use the downstairs distance<c entourage for OL. Equivariance identifies the projected orbit, expansivity forces p(a)=x, "
                + "and b=a is an OL tracer. Compactness and continuity make p uniformly continuous; the two preceding suppliers now prove SR from actual upstairs shadowing. "
                + "Neither zero-dimensionality nor surjectivity nor onto dynamics is assumed. This theorem proves SR; it does not replace it by ALP or assert that Peng's unrestricted factors are expansive."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(F.Id(name))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
}
