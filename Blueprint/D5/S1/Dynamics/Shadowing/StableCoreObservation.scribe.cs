using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class StableCoreObservationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/StableCoreObservation.";
    private static Formula X => F.Id("X");
    private static Formula DType => F.Id("D");
    private static Formula f => F.Id("f");
    private static Formula q => F.Id("q");
    private static Formula N => F.Id("N");
    private static Formula M => F.Id("M");
    private static Formula n => F.Id("n");
    private static Formula x => F.Id("x");
    private static Formula a => F.Id("a");
    private static Formula w => F.Id("w");
    private static Formula k => F.Id("k");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Map(Formula domain, Formula codomain) =>
        Seq(domain, Sp, Rightarrow, Sp, codomain);
    private static Formula All(Formula value, Formula type) =>
        Seq(Forall, Sp, value, Colon, Sp, type, Comma);
    private static Formula Inst(string name, Formula type) =>
        Seq(Grp(), OpenBracket, Call(name, type), CloseBracket);
    private static Formula Hyp(Formula premise) => Seq(premise, Sp, Rightarrow);
    private static Formula Iter(Formula time) => Call("Function.iterate", f, time);
    private static Formula Observe(Formula time, Formula point) =>
        Apply(q, Apply(Iter(time), point));
    private static Formula StableImage => Call("Set.iInter",
        Seq(n, Sp, Mapsto, Sp, Call("Set.range", Iter(n))));
    private static Formula Names => Call("Set.range",
        Seq(x, Sp, Mapsto, Sp, Open, n, Sp, Mapsto, Sp, Observe(n, x), Close));
    private static Formula CoreLaw => Seq(Open, Forall, Sp, a, Sp, InMacro, Sp,
        StableImage, Comma, Sp, Observe(M, a), Sp, Eq, Sp, Apply(q, a), Close);
    private static Formula TailLaw => Seq(Open, All(n, Nat), Sp, N, Sp, Le, Sp, n,
        Sp, Rightarrow, Sp, All(x, X), Sp,
        Observe(Seq(n, Plus, M), x), Sp, Eq, Sp, Observe(n, x), Close);
    private static Formula[] CompactSource(bool finite) => finite
        ? [Types(), Inst("TopologicalSpace", X), Inst("CompactSpace", X), Inst("T2Space", X),
            Inst("TopologicalSpace", DType), Inst("DiscreteTopology", DType), Inst("Finite", DType),
            Maps(), Hyp(Call("Continuous", f)), Hyp(Call("Continuous", q))]
        : [Types(), Inst("TopologicalSpace", X), Inst("CompactSpace", X), Inst("T2Space", X),
            Inst("TopologicalSpace", DType), Inst("DiscreteTopology", DType),
            Maps(), Hyp(Call("Continuous", f)), Hyp(Call("Continuous", q))];
    private static Formula Types() => Seq(All(X, F.Id("Type")), Sp, All(DType, F.Id("Type")));
    private static Formula Maps() => Seq(All(f, Map(X, X)), Sp, All(q, Map(X, DType)));
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stable-image observation period extends to a uniform exact tail; positive periods over finite alphabets then give finitely many complete names.",
        H("Stable Core and Complete Observation Names"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stable-core-uniform-observation-tail"),
                DeclarationHandle.Create(Owner + "finite_observation_eventually_periodic_of_stable_core_periodic"),
                H("From the stable image to one uniform tail"),
                StatementSource.FromAuthor(St([.. CompactSource(false),
                    All(M, Nat), Hyp(CoreLaw),
                    Seq(Exists, Sp, N, Colon, Sp, Nat, Comma, Sp, TailLaw)])),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "Let X be compact Hausdorff, f:X→X continuous, D any discrete space, and q:X→D continuous. "
                        + "The stable image is the intersection of the exact iterate ranges f^n(X), with n=0 included. "
                        + "Assume q(f^M(a))=q(a) at every stable-image point. One natural N then satisfies "
                        + "q(f^(n+M)(x))=q(f^n(x)) simultaneously for every x and every n≥N. "
                        + "M may be zero, and D need not be finite. No metric, countability, surjectivity, invertibility "
                        + "or source-shadowing assumption is introduced.")),
                    Paragraph(Text(
                        "The mismatch set B={x:q(f^M(x))≠q(x)} is closed because D is discrete. "
                        + "It misses the stable image by the supplied core law. If every proposed N failed, "
                        + "a violating point at a later iterate would belong to B and every earlier iterate range. "
                        + "The nested closed sets B∩f^n(X) would therefore have nonempty finite intersections; "
                        + "compactness would put a point in B and the stable image, a contradiction. "
                        + "This compactness argument constructs the uniform exact tail rather than assuming it.")),
                    Paragraph(Text(
                        "This is a repository-derived supplier for a restricted stable-core resolution inspired by Peng's "
                        + "zero-dimensional extension questions. The source/interface review found no matching supplier "
                        + "in the reviewed project dynamics/topology modules or pinned Mathlib topology/dynamics scope. "
                        + "That bounded library search does not certify worldwide novelty. The unrestricted Questions 5.1 "
                        + "and 5.2, the relative quotient, orbit lift and final inverse-limit construction remain unfinished."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventual-periodic-prefix-injection"),
                DeclarationHandle.Create(Owner + "finite_observation_name_injective_of_eventually_periodic"),
                H("Complete names are determined by a finite prefix"),
                StatementSource.FromAuthor(St(Types(), Maps(), All(N, Nat), All(M, Nat),
                    Hyp(Seq(D(0), Sp, Lt, Sp, M)), Hyp(TailLaw),
                    Call("Set.InjOn", Seq(w, Sp, Mapsto, Sp, Open, k, Colon, Sp,
                        Call("Fin", Seq(N, Plus, M)), Sp, Mapsto, Sp, Apply(w, k), Close), Names))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary types X and D, maps f and q, and a uniform tail law of positive period M, "
                        + "restriction to Fin(N+M) is injective on the exact range of complete names x↦(n↦q(f^n(x))). "
                        + "Neither topology nor finiteness of D is needed. Empty source and alphabet are retained. "
                        + "All times, including time zero and the transient segment before N, are observed.")),
                    Paragraph(Text(
                        "Strong induction on a time k compares two names. Below N+M their prefix equality pays the coordinate. "
                        + "At every later time, the tail law reduces k to k−M, which is at least N and strictly smaller than k. "
                        + "This reduction supplies exact whole-name injectivity, rather than only a finite-prefix realization "
                        + "or a finite-graph language inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-core-finite-whole-name-range"),
                DeclarationHandle.Create(Owner + "finite_observation_range_finite_of_stable_core_periodic"),
                H("A finite carrier of complete names"),
                StatementSource.FromAuthor(St([.. CompactSource(true), All(M, Nat),
                    Hyp(Seq(D(0), Sp, Lt, Sp, M)), Hyp(CoreLaw), Call("Set.Finite", Names)])),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the compact Hausdorff continuous system, a finite discrete alphabet and a positive stable-image "
                        + "observation period give a finite exact range of complete names. The preceding uniform-tail theorem "
                        + "provides N, and prefix injection embeds the name subtype into the finite function type Fin(N+M)→D. "
                        + "Transient source points are included; no replacement by names beginning only on the stable core is made.")),
                    Paragraph(Text(
                        "This finite carrier is the intended input to finite joint-observation stages and their all-time restriction "
                        + "bonds. The present module proves the carrier finiteness; it does not yet construct those stages, prove the "
                        + "orbit-range identity, or invoke the existing Mittag–Leffler shadowing theorem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        var items = new List<Formula> { F.Id(parts[0]) };
        for (var i = 1; i < parts.Length; i++) items.AddRange([Dot, F.Id(parts[i])]);
        return Apply(Seq(Operatorname, Grp([.. items])), arguments);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
