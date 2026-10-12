using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class StableCoreObservationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/StableCoreObservation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string x, Formula t) => Seq(Forall, Sp, V(x), Colon, Sp, t, Comma);
    private static Formula Inst(string c, Formula x) => Seq(OpenBracket, Call(c, x), CloseBracket);
    private static Formula Hyp(Formula p) => Seq(Grp(p), Sp, Rightarrow);
    private static Formula Sum => Seq(V("N"), Plus, V("M"));
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula NameRange => Call("Set.range", Call("nu", V("f"), V("q")));
    private static Formula CorePeriod => Seq(Forall, Sp, V("a"), InMacro,
        Call("stableCore", V("f")), Comma, Sp,
        Call("q", Call("iterate", V("f"), V("M"), V("a"))), Eq, Call("q", V("a")));
    private static Formula Tail => Seq(All("n", V("Nat")), Sp,
        V("N"), Le, Sp, V("n"), Sp, Rightarrow, Sp, All("x", V("X")), Sp,
        Call("q", Call("iterate", V("f"), Seq(V("n"), Plus, V("M")), V("x"))), Eq,
        Call("q", Call("iterate", V("f"), V("n"), V("x"))));
    private static Formula PrefixInjective => Call("Injective",
        Call("prefix", NameRange, Sum));
    private static Formula[] Telescope(bool finite) => [
        Seq(All("X", V("Type")), Sp, All("D", V("Type")), Sp,
            Inst("TopologicalSpace", V("X")), Sp, Inst("CompactSpace", V("X")), Sp,
            Inst("TTwoSpace", V("X"))),
        Seq(Grp(Inst("TopologicalSpace", V("D"))), Sp, Inst("DiscreteTopology", V("D")), Sp,
            finite ? Inst("Finite", V("D")) : Seq()),
        Seq(All("f", Map(V("X"), V("X"))), Sp, All("q", Map(V("X"), V("D"))), Sp,
            All("M", V("Nat"))),
        Hyp(Call("Continuous", V("f"))), Hyp(Call("Continuous", V("q"))) ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A period of a discrete observation on the stable core gives a uniform exact tail; a positive period and finite alphabet give a finite range of entire forward names.",
        H("Stable-Core Observations and Exact Prefix Coding"), Blocks(
        Describe.Lean(DescribeId.Create("stable-core"), DeclarationHandle.Create(Owner + "stableCore"),
            H("All forward images, including time zero"), StatementSource.FromAuthor(St(
                Seq(All("X", V("Type")), Sp, All("f", Map(V("X"), V("X")))),
                Seq(Call("stableCore", V("f")), Eq, Call("Intersection", Call("iterateRanges", V("f")))))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "stableCore(f) is the intersection, over all natural n including zero, of range(f^[n]). "
                + "The dynamics may be nononto. The definition makes no exchange of an image with an intersection."))),
            DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("uniform-exact-tail"),
            DeclarationHandle.Create(Owner + "finite_observation_eventually_periodic_of_stable_core_periodic"),
            H("A core observation period escapes to one uniform tail"),
            StatementSource.FromAuthor(St([.. Telescope(false), Hyp(CorePeriod),
                Seq(Exists, Sp, V("N"), Colon, Sp, V("Nat"), Comma, Sp, Tail)])),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text(
                    "Let X:Type u be compact Hausdorff and D:Type v discrete, with independent arbitrary universes. "
                    + "Let f:X→X and q:X→D be continuous. For any natural M, assume q(f^[M](a))=q(a) "
                    + "for every a in stableCore(f). Then there exists one natural N such that, for every n≥N "
                    + "and every x in X, q(f^[n+M](x))=q(f^[n](x)). Neither finiteness of D nor positivity of M is needed.")),
                Paragraph(Text(
                    "Put C={a:q(f^[M](a))≠q(a)}. The mismatch subset of D×D is closed because D is discrete, "
                    + "so continuity makes C closed. Every iterate image is compact and closed, and the sets "
                    + "C∩range(f^[n]) decrease. If each were nonempty, Mathlib's compact nested-intersection "
                    + "theorem would give a point in C∩stableCore(f), contradicting the core hypothesis. "
                    + "Thus the mismatch is absent from one whole image range(f^[N]). For n≥N, factor the "
                    + "iterate as f^[N] composed with f^[n-N] to place every f^[n](x) in that image. "
                    + "Applying the absence of mismatch there gives the claimed exact equality.")),
                Paragraph(Text(
                    "The finite whole-name theorem below consumes this supplier together with exact prefix injectivity. "
                    + "This theorem supplies a uniform tail, rather than assuming one or assuming finite whole names."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("exact-prefix-injective"),
            DeclarationHandle.Create(Owner + "forward_name_prefix_injective_of_eventually_periodic"),
            H("The exact N+M prefix determines every whole name"),
            StatementSource.FromAuthor(St(
                Seq(All("X", V("Type")), Sp, All("D", V("Type")), Sp,
                    All("f", Map(V("X"), V("X"))), Sp, All("q", Map(V("X"), V("D")))),
                Seq(All("N", V("Nat")), Sp, All("M", V("Nat"))),
                Hyp(Seq(D(0), Lt, V("M"))), Hyp(Tail), PrefixInjective)),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text(
                    "For arbitrary types X and D, arbitrary f and q, and naturals N,M with 0<M, assume the uniform tail "
                    + "equality for all n≥N and all x. Write nu(f,q)(x)(n)=q(f^[n](x)). Then the map from "
                    + "Set.range(nu(f,q)) to (Fin(N+M)→D), taking w to (i↦w(i)), is injective. "
                    + "This is a map on actual entire names, with all transient initial points and time zero retained. "
                    + "No topology, finiteness or nonemptiness is assumed in this theorem.")),
                Paragraph(Text(
                    "Given two names with the same prefix, use strong induction on k. For k<N+M use the prefix coordinate. "
                    + "Otherwise j=k-M satisfies N≤j and j<k because M>0. Both names have the same value at k as at j, "
                    + "so the induction hypothesis at j proves equality. Function and subtype extensionality give injectivity. "
                    + "The finite whole-name theorem consumes this induction result."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-whole-name-range"),
            DeclarationHandle.Create(Owner + "finite_observation_names_of_stable_core_periodic"),
            H("Whole-name finiteness and a cardinal bound"),
            StatementSource.FromAuthor(St([.. Telescope(true), Hyp(Seq(D(0), Lt, V("M"))), Hyp(CorePeriod),
                Seq(Exists, Sp, V("N"), Colon, Sp, V("Nat"), Comma, Sp,
                    Grp(Tail), Sp, Land, Sp, PrefixInjective, Sp, Land),
                Seq(Call("Set.Finite", NameRange), Sp, Land, Sp,
                    Call("Nat.card", NameRange), Le, Sp, Call("Nat.card", V("D")), Caret, Grp(Sum))])),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")), Blocks(
                Paragraph(Text(
                    "With the compact Hausdorff and continuous telescope of the tail theorem, additionally require "
                    + "Finite D and 0<M. The result supplies a single N, its exact uniform tail equality, "
                    + "injectivity of the prefix map to Fin(N+M)→D, Set.Finite of the entire forward-name range, "
                    + "and Nat.card(range(nu(f,q)))≤Nat.card(D)^(N+M). These natural cards denote genuine finite "
                    + "cardinalities here: the prefix target is finite and injectivity proves the name subtype finite. "
                    + "The proof reuses Mathlib's finite-type injection and function-cardinality theorems.")),
                Paragraph(Text(
                    "If X is empty, its entire name range is empty and every assertion remains valid. If D is empty, "
                    + "the existence of q forces X empty; N+M>0 makes the stated bound compatible with the empty alphabet. "
                    + "No Nonempty instance, onto dynamics, recurrent-state pruning, or positive global period of f is used.")),
                Paragraph(Text(
                    "This supplies the first stage of the stable-core resolution R: every later finite joint observation "
                    + "whose core period is established gets a finite exact-name state space. Still required are onto core "
                    + "dynamics, observation periods from forward equicontinuity, the relative zero-dimensional resolution, "
                    + "the orbit lift and exact stable-image identification, the full all-observation diagram with whole-path "
                    + "lifting and inverse-limit conjugacy, and shadowing of the extension. R as a whole and unrestricted "
                    + "Peng Questions 5.1 and 5.2 are not formalized by this supplier. The elementary compactness and "
                    + "induction arguments carry no literature originality or worldwide-open claim.")),
                Paragraph(Text(
                    "All declarations have utility kind none: these are abstract compactness and induction results, "
                    + "not a finite certified instance, enumeration, checker or numerical reduction. The S1 whole-name "
                    + "expression is the definitional expansion of the existing S3 completeItinerary; no reverse-stratum "
                    + "import or duplicate named definition is introduced."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        var operatorItems = new List<Formula> { V(parts[0]) };
        for (var i = 1; i < parts.Length; i++) operatorItems.AddRange([Dot, V(parts[i])]);
        var items = new List<Formula> { Seq(Operatorname, Grp([.. operatorItems])), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
