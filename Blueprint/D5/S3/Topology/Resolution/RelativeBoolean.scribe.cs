using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Resolution;

internal sealed class RelativeBooleanDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Resolution/RelativeBoolean.";
    private static Formula V(string n) => F.Id(n);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Inst(string n, Formula t) => Seq(Grp(), OpenBracket, Call(n, t), CloseBracket, Sp);
    private static Formula Hyp(Formula p) => Seq(p, Sp, Rightarrow, Sp);
    private static Formula Y => Call("Space", V("C"));
    private static Formula Pi => Call("projection", V("C"));
    private static Formula Lift(string h, string hh, string hC) => Call("lift", V(h), V(hh), V(hC));
    private static Formula[] Source => [
        Seq(All("X", Call("Type", V("u"))), Inst("TopologicalSpace", V("X"))),
        All("C", Call("Set", V("X")))
    ];
    private static Formula[] Compact => [
        Inst("CompactSpace", V("X")), Inst("T2Space", V("X")),
        Hyp(Call("IsClosed", V("C"))), Inst("TotallyDisconnectedSpace", V("C"))
    ];
    private static Formula Basis => Call("IsTopologicalBasis",
        Call("setOf", Seq(V("U"), Colon, Sp, Call("Set", Y), Sp, Mapsto, Sp, Call("IsClopen", V("U")))));
    private static Formula Main => Disp(new Formula.Aligned([
        .. Source, .. Compact,
        Seq(All("Xprime", Call("Type", V("v"))), Inst("TopologicalSpace", V("Xprime")),
            All("Cprime", Call("Set", V("Xprime")))),
        Seq(All("Xbis", Call("Type", V("w"))), Inst("TopologicalSpace", V("Xbis")),
            All("Cbis", Call("Set", V("Xbis")))),
        Seq(All("h", Fn(V("X"), V("Xprime"))), All("hh", Call("Continuous", V("h"))),
            All("hC", Call("MapsTo", V("h"), V("C"), V("Cprime")))),
        Seq(All("k", Fn(V("Xprime"), V("Xbis"))), All("hk", Call("Continuous", V("k"))),
            All("kC", Call("MapsTo", V("k"), V("Cprime"), V("Cbis")))),
        Seq(Call("CompactSpace", Y), Sp, Land, Sp, Call("T2Space", Y), Sp, Land, Sp, Basis, Sp, Land),
        Seq(Call("Continuous", Pi), Sp, Land, Sp, Call("Surjective", Pi), Sp, Land,
            Sp, Call("Continuous", Lift("h", "hh", "hC")), Sp, Land),
        Seq(Call("lift", V("id"), V("continuousId"), Call("mapsToId", V("C"))), Sp, Eq, Sp, V("id"), Sp, Land),
        Seq(Call("lift", Call("compose", V("k"), V("h")), Call("comp", V("hk"), V("hh")),
                Call("comp", V("kC"), V("hC"))), Sp, Eq, Sp,
            Call("compose", Lift("k", "hk", "kC"), Lift("h", "hh", "hC")))
    ]));
    private static Formula Shrinking => Disp(new Formula.Aligned([
        .. Source, .. Compact,
        Seq(All("U", Call("Set", V("X"))), Hyp(Call("IsOpen", V("U"))),
            All("x", V("X")), Hyp(Seq(V("x"), Sp, InMacro, Sp, V("U")))),
        Seq(Exists, Sp, V("V"), Colon, Sp, Call("Set", V("X")), Comma, Sp,
            Call("IsOpen", V("V")), Sp, Land, Sp, V("x"), Sp, InMacro, Sp, V("V"), Sp, Land),
        Seq(Call("closure", V("V")), Sp, Subseteq, Sp, V("U"), Sp, Land, Sp,
            Forall, Sp, V("c"), Sp, InMacro, Sp, V("C"), Comma, Sp,
            Neg, Grp(Seq(V("c"), Sp, InMacro, Sp, Call("frontier", V("V")))))
    ]));
    private static Formula Fiber => Disp(new Formula.Aligned([
        .. Source, Seq(All("c", V("X")), Hyp(Seq(V("c"), Sp, InMacro, Sp, V("C")))),
        Seq(Call("preimage", Pi, Call("singleton", V("c"))), Sp, Eq, Sp,
            Call("singleton", Call("point", V("C"), V("c"))))
    ]));
    private static Formula Homeomorphism => Disp(new Formula.Aligned([
        .. Source,
        Seq(Call("coreHomeomorph", V("C")), Colon, Sp,
            Call("Homeomorph", V("C"), Call("subtype", Seq(V("y"), Colon, Sp, Y, Sp,
                Mapsto, Sp, Call("apply", Pi, V("y")), Sp, InMacro, Sp, V("C")))))
    ]));
    private static AssessedProvenance SourceProvenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/banaschewski1955nulldimensional"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closure of the actual boundary-avoiding membership graph gives a compact zero-dimensional relative resolution with coherent continuous pair-map lifts.",
        H("Relative Boolean graph resolution"), Blocks(
            Paragraph(Text("Observation(C) consists of all actual subsets A of X whose ambient frontier misses every point of C. "
                + "Cube(C) is Observation(C)→Bool, with Bool discrete. evaluation(C,x)(A) is actual membership of x in A, "
                + "including nonopen A. graph(C,x)=(x,evaluation(C,x)); carrier(C) is the closure of its range in X×Cube(C), "
                + "and Space(C) is that closed subtype. point(C,x) is the actual graph point, projection(C) is its first coordinate, "
                + "and coordinates(C) is the cube coordinate. Global continuity of evaluation or graph is not assumed.")),
            Describe.Lean(DescribeId.Create("boundary-avoiding-shrinking"),
                DeclarationHandle.Create(Owner + "exists_open_closure_subset_avoiding_frontier"),
                H("Separating neighborhoods avoiding the core boundary"), StatementSource.FromAuthor(Shrinking),
                SourceProvenance, Blocks(Paragraph(Text("Off C, shrink the closed singleton inside U minus C. On C, choose a clopen D in the compact subspace C "
                    + "containing x and contained in U. The ambient images K of D and L of its complement are closed. Normal shrinking gives "
                    + "K⊆V⊆closure(V)⊆U minus L. Points of D are inside V and all other core points are outside its closure. "
                    + "The frontier therefore misses C. This covers every x in U, including the cases C empty and D equal to all C."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compact-functorial-resolution"),
                DeclarationHandle.Create(Owner + "functorial_resolution"),
                H("The actual resolution and coherent lifts"), StatementSource.FromAuthor(Main), SourceProvenance,
                Blocks(
                    Paragraph(Text("X, Xprime and Xbis have independent universe levels u, v and w. The compact Hausdorff and closed zero-dimensional hypotheses "
                        + "are imposed only on the source pair (X,C). The pair maps h and k are continuous and send their distinguished subsets into the next ones. "
                        + "No compactness or separation is needed for their codomains to construct the lifts. compose(k,h) means k after h.")),
                    Paragraph(Text("Every bit of a closure point constrains its base point: bit true puts it in closure(A), and bit false in closure(complement A). "
                        + "An explicit closed union containing the entire graph proves these constraints. The separating-neighborhood lemma then rules out "
                        + "different base points with identical cube coordinates. Thus coordinates(C) is injective. Compactness makes it a closed embedding into "
                        + "the binary cube; total disconnectedness pulls back, and the compact Hausdorff clopen-basis theorem gives the displayed basis. "
                        + "The ambient X×Cube(C) is not assumed zero-dimensional.")),
                    Paragraph(Text("Compactness and Hausdorffness of Space(C) come from the closed subtype of the compact Hausdorff product. "
                        + "The actual graph points witness surjectivity of projection(C), even when graph is discontinuous. Empty X yields empty Space(C).")),
                    Paragraph(Text("For an admissible target A, pullback(h,A) is the actual inverse image. Continuous.frontier_preimage_subset proves its admissibility. "
                        + "ambientMap(h) sends (x,t) to (h(x), A↦t(pullback(h,A))). Coordinatewise continuity makes this ambient map continuous. "
                        + "It sends each actual graph point to graph(Cprime,h(x)); MapsTo.closure therefore restricts it to lift(h,hh,hC). "
                        + "Projection commutes with h and lift sends point(C,x) to point(Cprime,h(x)). Identity and composition are exact equalities "
                        + "of these same subtype functions, using identity and composition of actual inverse images. Neither openness nor injectivity nor surjectivity of h or k is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-core-fibers"), DeclarationHandle.Create(Owner + "fiber_singleton"),
                H("Singleton fibers at distinguished points"), StatementSource.FromAuthor(Fiber), SourceProvenance,
                Blocks(Paragraph(Text("This theorem needs only a topological X and c in C. Since c avoids every admissible frontier, membership in each A or its complement "
                    + "places c in the corresponding interior. The forced-coordinate constraints determine every bit to be evaluation(C,c). "
                    + "Thus every point over c equals the actual graph point point(C,c). Compactness, closedness and zero-dimensionality of C are unnecessary for this fiber assertion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-core-homeomorphism"), DeclarationHandle.Create(Owner + "coreHomeomorph"),
                H("The full inverse image of the core"), StatementSource.FromAuthor(Homeomorphism), SourceProvenance,
                Blocks(Paragraph(Text("sectionC(C) sends a subtype point c of C to point(C,c). For each admissible A the trace of A on C is clopen: "
                    + "its two membership choices are locally constant at every c. The indicator continuity criterion and product continuity prove the actual section continuous. "
                    + "coreHomeomorph(C) uses this section as forward map and projection as inverse on the full inverse image. "
                    + "The inverse laws use the singleton-fiber theorem. This homeomorphism also needs only a topological X."))), DescribeRole.Definition),
            Paragraph(Text("The underlying compactification is classical Stone/Banaschewski, interpreted through the Michael modification. "
                + "The bibliographic source and inspected scope are in Library/Topology/banaschewski1955nulldimensional.md. "
                + "The explicit relative construction and proofs here make no novelty claim. No shadowing, finite-name, period or unrestricted Peng Question 5.1 result is asserted.")))));
}
