using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class MittagLefflerInverseLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite open cover shadowing passes to arbitrary directed compact Hausdorff limits "
            + "with stabilized bonding images.",
        H("Shadowing of Mittag-Leffler Inverse Limits"),
        Blocks(
            Paragraph(Text(
                "A pseudo-orbit x has each pair f(x(n)), x(n+1) in one member of a control "
                + "cover. A point z traces it when f iterated n times at z and x(n) share a "
                + "member of the output cover for every natural n, including zero. Shadowing "
                + "quantifies over every finite open output cover and all pseudo-orbits.")),
            Paragraph(Text(
                "The stages form a small nonempty cofiltered thin category. In particular, "
                + "the opposite of any nonempty directed preorder is allowed. Every stage is "
                + "compact Hausdorff. Bonding maps are continuous and satisfy the functor "
                + "laws; the continuous stage dynamics form a natural endomorphism. There is "
                + "no metric, countable cofinal family, invertibility, or onto-map hypothesis.")),
            Describe.Lean(
                DescribeId.Create("compact-limit-projection-image"),
                DeclarationHandle.Create(Owner + "compact_projection_image"),
                H("Projection images are intersections of incoming images"),
                StatementSource.FromAuthor(Disp(ProjectionStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonempty stages, S(i) is the intersection of all incoming bonding "
                    + "images. Fix a in S(i). Impose every compatibility equation and the "
                    + "fiber condition x(i)=a in the compact product. A finite collection is "
                    + "realized by taking a preimage of a at a common finer stage and mapping "
                    + "it to every mentioned coordinate. Compactness supplies a full compatible "
                    + "thread. Conversely, every thread lies in every incoming image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-cover-single-stage-descent"),
                DeclarationHandle.Create(Owner + "finite_cover_descent"),
                H("Every finite cover is observed at one stage"),
                StatementSource.FromAuthor(Disp(DescentStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here C is any finite open cover of the limit L, and union(V) is the "
                    + "union of the finite family V of stage opens. Single-coordinate inverse "
                    + "images of stage opens form a basis of the "
                    + "cofiltered limit. Choose such a neighborhood inside a cover member at "
                    + "each point, take a finite subcover, and move their finitely many stage "
                    + "indices to a common finer stage i. The resulting finite family V covers "
                    + "the actual projection image, and each pulled-back open lies in an "
                    + "original cover member. The projection need not be onto its stage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ml-inverse-limit-shadowing"),
                DeclarationHandle.Create(Owner + "shadowing_inverse_limit_of_mittag_leffler"),
                H("Mittag-Leffler inverse limits preserve shadowing"),
                StatementSource.FromAuthor(Disp(ShadowingStatement())),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/goodmeddaugh2020shadowing"),
                    LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "Assume every stage dynamics has finite-cover shadowing and the "
                        + "bonding images satisfy Mittag-Leffler stabilization: for each i "
                        + "some k above i has the same image in i as every stage above k. "
                        + "Then the coordinatewise dynamics on the full compatible-thread "
                        + "limit has finite-cover shadowing.")),
                    Paragraph(Text(
                        "Descend an output cover to i, then choose an image-stabilizing "
                        + "bond k to i. Pulling the descended opens back covers the entire "
                        + "original stage k. Shadow the projected pseudo-orbit there. Its "
                        + "shadowing point b need not lift at k. Its image at i belongs to "
                        + "S(i), so the projection-image theorem lifts that coarse point "
                        + "to a full thread z. Naturality at every iterate transfers tracing "
                        + "back to the output cover. No assertion about shadowing restricted "
                        + "to eventual images is needed.")),
                    Paragraph(Text(
                        "If a stage is empty, the limit is empty and every pseudo-orbit "
                        + "condition is vacuous. Thus the preservation theorem includes "
                        + "empty stages without an extra nonemptiness hypothesis.")),
                    Paragraph(Text(
                        "This formalizes the inverse-limit preservation theorem of Good and "
                        + "Meddaugh, Inventiones mathematicae 220 (2020), Theorem 8, pp.722-723. "
                        + "Their final Definitions 2-4 allow nonsurjective continuous bonding "
                        + "maps and impose Mittag-Leffler stabilization over arbitrary directed "
                        + "indices. The Lean proof implements the coarse-image lifting argument "
                        + "on a cofiltered thin category, and includes the vacuous empty-stage "
                        + "case. This is attributed known-background infrastructure.")),
                    Paragraph(Text(
                        "Peng's Question 5.1 asks for a zero-dimensional shadowing extension "
                        + "of every compact Hausdorff shadowing system. This preservation "
                        + "theorem does not construct its coherent all-face symbolic diagram. "
                        + "Simultaneous lifts, sound decoding, and coding of every original "
                        + "orbit remain necessary for that route."))),
                DescribeRole.Theorem))));

    private static StrataLint.Scribe.Formula Name(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));

    private static StrataLint.Scribe.Formula Call(string name, StrataLint.Scribe.Formula arg) =>
        Seq(Name(name), Open, arg, Close);

    private static StrataLint.Scribe.Formula All(string name,
        StrataLint.Scribe.Formula type, StrataLint.Scribe.Formula body) =>
        Seq(Forall, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static StrataLint.Scribe.Formula Some(string name,
        StrataLint.Scribe.Formula type, StrataLint.Scribe.Formula body) =>
        Seq(Exists, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static StrataLint.Scribe.Formula Instance(StrataLint.Scribe.Formula type,
        StrataLint.Scribe.Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);

    private static StrataLint.Scribe.Formula Stage(string name) =>
        Seq(F.Id("F"), Dot, Name("obj"), Open, F.Id(name), Close);

    private static StrataLint.Scribe.Formula Limit() =>
        Seq(Name("TopCat"), Dot, Call("limitCone", F.Id("F")), Dot, Name("pt"));

    private static StrataLint.Scribe.Formula Projection() =>
        Seq(Name("TopCat"), Dot, Call("limitCone", F.Id("F")), Dot, Pi,
            Dot, Call("app", F.Id("i")));

    private static StrataLint.Scribe.Formula OpenCover() =>
        Call("IsOpenCover", Seq(Open, LambdaLower, Sp, Open, F.Id("U"), Colon, Sp,
            F.Id("C"), Close, Sp, Mapsto, Sp, F.Id("U"), Dot, Name("val"), Close));

    private static StrataLint.Scribe.Formula Context(bool thin, bool nonempty,
        StrataLint.Scribe.Formula body)
    {
        body = Instance(All("j", F.Id("J"), Seq(Operatorname, Grp(F.Id("T"), D(2), F.Id("Space")), Open, Stage("j"), Close)), body);
        body = Instance(All("j", F.Id("J"), Call("CompactSpace", Stage("j"))), body);
        if (nonempty)
            body = Instance(All("j", F.Id("J"), Call("Nonempty", Stage("j"))), body);
        if (thin)
            body = Instance(Seq(Name("Quiver"), Dot, Call("IsThin", F.Id("J"))), body);
        body = Instance(Call("IsCofiltered", F.Id("J")), body);
        body = All("F", Call("Functor", Seq(F.Id("J"), Comma, Sp, Name("TopCat"), Caret,
            Grp(Call("max", Seq(F.Id("u"), Comma, Sp, F.Id("v")))))), body);
        body = Instance(Call("SmallCategory", F.Id("J")), body);
        body = All("J", Seq(Name("Type"), Underscore, F.Id("u")), body);
        return All("u", Name("Universe"), All("v", Name("Universe"), body));
    }

    private static StrataLint.Scribe.Formula ProjectionStatement() =>
        Context(true, true, All("i", F.Id("J"), Seq(
            Call("range", Projection()), Sp, Eq, Sp,
            Seq(Name("Functor"), Dot, Call("comp", Seq(F.Id("F"), Comma, Sp, Call("forget", Name("TopCat"))))),
            Dot, Call("eventualRange", F.Id("i")))));

    private static StrataLint.Scribe.Formula DescentStatement()
    {
        var coversImage = All("a", Stage("i"), Seq(
            F.Id("a"), Sp, InMacro, Sp, Call("range", Projection()), Sp, Implies, Sp,
            Some("U", Call("Opens", Stage("i")), Seq(
                F.Id("U"), Sp, InMacro, Sp, F.Id("V"), Sp, Land, Sp,
                F.Id("a"), Sp, InMacro, Sp, F.Id("U")))));
        var refines = All("U", Call("Opens", Stage("i")), Seq(
            F.Id("U"), Sp, InMacro, Sp, F.Id("V"), Sp, Implies, Sp,
            Some("W", Call("Opens", Limit()), Seq(
                F.Id("W"), Sp, InMacro, Sp, F.Id("C"), Sp, Land, Sp,
                Projection(), Caret, Grp(Minus, D(1)), Open,
                F.Id("U"), Colon, Sp, Call("Set", Stage("i")), Close,
                Sp, Subseteq, Sp, Open, F.Id("W"), Colon, Sp,
                Call("Set", Limit()), Close))));
        var conclusion = Some("i", F.Id("J"),
            Some("V", Call("Finset", Call("Opens", Stage("i"))),
                Seq(Open, coversImage, Close, Sp, Land, Sp, Open, refines, Close)));
        return Context(false, false, All("C", Call("Finset", Call("Opens", Limit())),
            Seq(OpenCover(), Sp, Implies, Sp, conclusion)));
    }

    private static StrataLint.Scribe.Formula ShadowingStatement() =>
        Context(true, false, All("d", Call("NatTrans", Seq(F.Id("F"), Comma, Sp, F.Id("F"))), Seq(
            Seq(Name("Functor"), Dot, Call("comp", Seq(F.Id("F"), Comma, Sp, Call("forget", Name("TopCat"))))),
            Dot, Name("IsMittagLeffler"), Sp, Implies, Sp,
            Open, All("j", F.Id("J"), Call("HasShadowing", Seq(
                F.Id("d"), Dot, Call("app", F.Id("j"))))), Close, Sp, Implies, Sp,
            Call("HasShadowing", Call("limitDynamics", Seq(F.Id("F"), Comma, Sp, F.Id("d")))))));
}
