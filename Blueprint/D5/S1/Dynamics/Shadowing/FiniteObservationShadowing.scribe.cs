using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteObservationShadowingDocument : IScribeDocumentDefinition
{
    private static Formula X => F.Id("X");
    private static Formula f => F.Id("f");
    private static Formula q => F.Id("q");
    private static Formula m => F.Id("m");
    private static Formula n => F.Id("n");
    private static Formula x => F.Id("x");
    private static Formula a => F.Id("a");
    private static Formula C => F.Id("C");
    private static Formula DType => F.Id("D");
    private static Formula U => F.Id("U");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Map(Formula s, Formula t) => Seq(s, Sp, Rightarrow, Sp, t);
    private static Formula All(Formula v, Formula t) => Seq(Forall, Sp, v, Colon, Sp, t, Comma);
    private static Formula Hyp(Formula p) => Seq(p, Sp, Rightarrow);
    private static Formula Inst(string name) => Seq(Grp(), OpenBracket, Call(name, X), CloseBracket);
    private static Formula Cover(Formula c) => Call("IsOpenCover",
        Seq(U, Colon, Sp, c, Sp, Mapsto, Sp, Call("Subtype.val", U)));
    private static Formula Statement => Disp(new Formula.Aligned([
        All(X, F.Id("Type")), Inst("TopologicalSpace"), Inst("CompactSpace"),
        Inst("T2Space"), Inst("TotallyDisconnectedSpace"), All(f, Map(X, X)),
        Hyp(Call("Continuous", f)),
        Hyp(Seq(Open, All(m, Nat), Sp, All(q, Map(X, Call("Fin", m))), Sp,
            Call("Continuous", q), Sp, Rightarrow, Sp,
            Call("Set.Finite", Call("Set.range", Seq(x, Sp, Mapsto, Sp, Open,
                n, Sp, Mapsto, Sp, Apply(q, Apply(Call("Function.iterate", f, n), x)), Close))), Close)),
        All(C, Call("Finset", Call("Opens", X))), Hyp(Cover(C)),
        Seq(Exists, Sp, DType, Colon, Sp, Call("Finset", Call("Opens", X)), Comma, Sp,
            Cover(DType), Sp, Land, Sp, All(a, Map(Nat, X)), Sp,
            Call("PseudoOrbit", f, DType, a), Sp, Rightarrow, Sp,
            Call("Shadows", f, C, a, Apply(a, D(0))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finitely many complete names for every finite continuous observation yield an actual finite open control cover and tracing by the initial point.",
        H("Finite Complete Names and Initial-Point Tracing"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-complete-names-initial-point-tracing"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteObservationShadowing.initial_point_tracing_of_finite_observation_names"),
            H("Constructing the control cover"),
            StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
            Blocks(
                Paragraph(Text(
                    "Let X be compact Hausdorff and zero-dimensional, with continuous f:X→X. "
                    + "Assume that for each natural m and each continuous q:X→Fin m, the exact range "
                    + "of complete names x↦(n↦q(f^n(x))) is finite. For every finite open cover C, "
                    + "there is a finite open cover D such that every D-pseudo-orbit a is C-shadowed "
                    + "by a(0), simultaneously at all natural times including zero. IsOpenCover in "
                    + "the formula is applied to U↦U.val with U ranging over the indicated finset. "
                    + "PseudoOrbit and Shadows are the existing finite-open-cover contracts. "
                    + "The compact Hausdorff totally disconnected hypothesis supplies a clopen basis. "
                    + "There is no metric, countability, nonempty, surjectivity or invertibility assumption.")),
                Paragraph(Text(
                    "Refine C by a finite disjoint clopen partition W indexed by Fin m, using Mathlib's "
                    + "IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover. The unique cell containing x "
                    + "defines q(x); each cell is open, so q is locally constant and continuous. "
                    + "The existing continuous_observationName theorem makes the complete-name map continuous. "
                    + "Its range S is finite by hypothesis and Hausdorff as a subspace of the product of "
                    + "discrete alphabets; hence S is discrete. The inverse images of singleton names are "
                    + "open and form the finite cover D. This constructs D from the observations.")),
                Paragraph(Text(
                    "A D-controlled error pair f(a(n)),a(n+1) lies in one complete-name fiber, so their "
                    + "names are equal. The name of f(x) is the left shift of the name of x. Induction "
                    + "therefore identifies the complete names of a(n) and f^n(a(0)). At coordinate zero "
                    + "these points have the same partition label. Their common clopen cell lies inside "
                    + "one member of C, proving tracing. The proof includes empty sources and empty name "
                    + "images without choosing an initial point unless a pseudo-orbit is already supplied.")),
                Paragraph(Text(
                    "This repository-derived construction fills the inference between finite complete "
                    + "observations and finite-cover tracing. StableCoreObservation's "
                    + "finite_observation_range_finite_of_stable_core_periodic supplies the hypothesis when "
                    + "each finite continuous observation has a positive period on the stable image; the "
                    + "period may depend on that observation. Substituting this supplier and choosing a(0) "
                    + "as the tracing point gives HasShadowing. This application introduces no additional "
                    + "mathematical declaration. Neither it nor the present inference constructs a relative "
                    + "Boolean extension or resolves Peng's general Question 5.1."))),
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
