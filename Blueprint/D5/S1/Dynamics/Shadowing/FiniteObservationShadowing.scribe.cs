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
                    "The theorem above converts finite complete observations into finite-cover tracing. "
                    + "For an application constructing a shadowing extension, let X be any compact Hausdorff "
                    + "space, f:X→X continuous, and K=⋂_{n∈ℕ}f^n(X), including n=0. Assume that the actual "
                    + "core K is zero-dimensional and that the iterates of T=StableRange.restriction f:K→K "
                    + "are equicontinuous. The exact hypotheses are TotallyDisconnectedSpace K and "
                    + "Equicontinuous (fun n : ℕ => T^[n]); compact Hausdorff K turns the former into a "
                    + "clopen basis. These core hypotheses yield the extension described below. Empty and "
                    + "nonmetrizable spaces are included, with no countability, ambient surjectivity, "
                    + "injectivity, invertibility or source-shadowing assumption.")),
                Paragraph(Text(
                    "Equicontinuity uses the compatible compact Hausdorff uniformity. Starting with "
                    + "UniformSpace X uses its own topology; starting with a compact Hausdorff topology, "
                    + "uniformSpaceOfCompactR1 supplies a uniformity whose topology is definitionally the "
                    + "given one, on X or directly on its closed core K. This preserves topology and is "
                    + "not a metrization. The subtype uniformity on K is compatible. If the hypothesis is "
                    + "instead Equicontinuous (fun (n : ℕ) (c : K) => f^[n] c.val), the actual subtype "
                    + "inclusion semiconjugates T with f. Semiconj.iterate_right identifies its composite "
                    + "with T^[n] with that ambient-valued family; the subtype uniform embedding's "
                    + "IsUniformInducing.equicontinuous_iff gives exactly the required equicontinuity of "
                    + "T's iterates. UniformEquicontinuous first gives Equicontinuous by .equicontinuous.")),
                Paragraph(Text(
                    "Each iterate image f^n(X) is compact and closed, so StableRange.is_closed_core "
                    + "makes K closed and compact. StableRange.compact_surjective_restriction supplies "
                    + "continuity and surjectivity of this actual T. Indeed, for c∈K the nested nonempty "
                    + "closed sets f^n(X)∩f⁻¹({c}) have a common point by compactness, giving a preimage "
                    + "in K. A core point is supplied before a preimage is chosen, so the argument "
                    + "also covers the empty case.")),
                Paragraph(Text(
                    "Let B_K consist of all actual subsets A⊆X whose ambient frontier misses K. Put "
                    + "e(x)(A)=1_A(x), j(x)=(x,e(x)), and Y=closure(j(X))⊆X×{false,true}^{B_K}; "
                    + "this is RelativeBoolean.Space K, with the binary coordinates discrete. Let "
                    + "π=RelativeBoolean.projection K and s=RelativeBoolean.sectionC K, so s(c)=j(c). "
                    + "The closed product subtype Y is compact Hausdorff, π is continuous and onto, "
                    + "and s is continuous since every admissible indicator is locally constant at K. "
                    + "The graph j need not be continuous on X. Zero-dimensionality of Y comes from "
                    + "its cube-coordinate embedding: clopen neighborhoods in K and normal shrinking "
                    + "give separating ambient neighborhoods whose frontiers miss K. The resulting "
                    + "Boolean coordinates separate first coordinates, so the cube projection is "
                    + "injective, hence a closed embedding by compactness. Its clopen basis pulls back "
                    + "to Y; zero-dimensionality is not inferred from the product with X.")),
                Paragraph(Text(
                    "Forward invariance of K makes inverse image under f preserve B_K. The continuous "
                    + "ambient map (x,t)↦(f(x), A↦t(f⁻¹(A))) preserves the graph closure and restricts to "
                    + "g=RelativeBoolean.stableLift f hf. Thus π∘g=f∘π and g∘s=s∘T, and both identities "
                    + "iterate at every natural time, including zero. At c∈K every coordinate over c "
                    + "is forced to equal e(c), giving π⁻¹({c})={RelativeBoolean.point K c} and "
                    + "π(s(c))=c.val. In particular every y with π(y)∈K equals s(⟨π(y),membership⟩).")),
                Paragraph(Text(
                    "The exact lifted core is K_g=⋂_{n∈ℕ}g^n(Y)=π⁻¹(K)=range(s). For the first "
                    + "inclusion, project any upstairs n-step preimage. Conversely, when π(y)∈K, "
                    + "choose x with f^n(x)=π(y); then g^n(j(x)) and y lie in the same singleton fiber, "
                    + "so they are equal. Each finite n is handled separately. This is "
                    + "RelativeBoolean.stable_range_lift_eq_preimage, followed by the section identity. "
                    + "The map c↦⟨s(c),membership⟩ is a homeomorphism K→K_g with inverse induced by π; "
                    + "the singleton-fiber identities give its inverse laws, and continuity comes from "
                    + "s and π. It conjugates T with the actual restriction of g to K_g.")),
                Paragraph(Text(
                    "Fix a continuous finite observer q:Y→Fin m and put Q=q∘s. Applying "
                    + "finite_observation_period_of_equicontinuous_surjective to T and Q gives M>0 "
                    + "with Q(T^M(c))=Q(c) for every c∈K. Equicontinuity makes the complete Q-name map "
                    + "locally constant; compactness makes its image finite. Surjectivity of T makes "
                    + "shift on that image a finite permutation, whose positive exponent supplies M. "
                    + "For y∈K_g write y=s(c); the iterated section identity gives "
                    + "q(g^M(y))=q(s(T^M(c)))=q(s(c))=q(y). M may depend on q; no common point period "
                    + "on the whole core is required. This transfer uses s directly and requires no "
                    + "uniform structure on Y or K_g.")),
                Paragraph(Text(
                    "Now finite_observation_range_finite_of_stable_core_periodic applies to this "
                    + "derived positive period on the exact core of g. It gives finiteness of the "
                    + "whole-space range { (n↦q(g^n(y))) : y∈Y }, including transient points. The "
                    + "closed mismatch set {y : q(g^M(y))≠q(y)} misses K_g; compactness makes it miss "
                    + "some iterate image g^N(Y). Every name is therefore M-periodic after N and is "
                    + "determined by its first N+M symbols. Neither this finiteness nor a core period "
                    + "was assumed.")),
                Paragraph(Text(
                    "Apply initial_point_tracing_of_finite_observation_names on this compact "
                    + "Hausdorff zero-dimensional Y. For every finite open cover C it constructs an "
                    + "actual finite open control cover D from the singleton complete-name fibers of "
                    + "a clopen partition refining C, as above. Every D-pseudo-orbit a is C-shadowed "
                    + "by a(0) at every natural time. Taking a(0) as the tracing witness gives "
                    + "HasShadowing g, with continuous onto factor π. An initial point is used only "
                    + "after a pseudo-orbit is supplied, so no nonempty-space guard is needed.")),
                Paragraph(Text(
                    "The boundary-avoiding Boolean compactification follows the classical "
                    + "Stone/Banaschewski picture of the Michael modification, which isolates X "
                    + "outside K and retains the original neighborhoods at K. The bibliographic "
                    + "attribution is Bernhard Banaschewski, Über nulldimensionale Räume, "
                    + "Mathematische Nachrichten 13 (1955), 129–140, DOI 10.1002/mana.19550130302, "
                    + "as recorded in Library/Topology/banaschewski1955nulldimensional.md. The "
                    + "original article has not been inspected; no theorem number or exact relative "
                    + "formulation is attributed to it. A universal-property characterization is "
                    + "explanatory context, not an additional formalized theorem. The explicit "
                    + "relative graph and stable-range arguments are repository derivations.")),
                Paragraph(Text(
                    "This application is a sufficient criterion for zero-dimensional equicontinuous "
                    + "actual stable cores. It does not show that every shadowing system has these "
                    + "core properties. No equicontinuity conclusion for the whole upstairs map g "
                    + "is asserted. Peng's unrestricted Question 5.1 and the simultaneous finite-face "
                    + "construction of Question 5.2 remain unresolved."))),
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
