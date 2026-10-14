using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Resolution;

internal sealed class StoneanFiniteClosedRefinementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, string type) =>
        Seq(Grp(), OpenBracket, Call(name, V(type)), CloseBracket, Sp);
    private static Formula Spaces => Seq(
        All("u", V("UniverseLevel")), All("v", V("UniverseLevel")),
        All("T", Seq(V("Type"), Underscore, Grp(V("u")))),
        All("B", Seq(V("Type"), Underscore, Grp(V("v")))),
        Inst("TopologicalSpace", "T"), Inst("TopologicalSpace", "B"),
        Inst("RegularSpace", "T"), Inst("ExtremallyDisconnected", "B"));
    private static Formula Map => Seq(All("p", Fn(V("T"), V("B"))),
        Call("Continuous", V("p")), Sp, Land, Sp, Call("IsOpenMap", V("p")),
        Sp, Land, Sp, Call("IsClosedMap", V("p")), Sp, Rightarrow, Sp);
    private static Formula LocalStatement => Disp(new Formula.Aligned([
        Spaces,
        Map,
        Seq(All("W", Call("Set", V("T"))), Call("IsOpen", V("W")),
            Sp, Rightarrow, Sp,
            Call("IsOpenMap", Call("compose", V("p"),
                Call("subtypeVal", Call("closure", V("W"))))))
    ]));
    private static Formula RefinementStatement => Disp(new Formula.Aligned([
        Seq(Spaces, Inst("NormalSpace", "T")),
        Map,
        Seq(All("n", V("Nat")), All("U", Fn(Call("Fin", V("n")), Call("Set", V("T"))))),
        Seq(Grp(Seq(All("i", Call("Fin", V("n"))), Call("IsOpen", Call("U", V("i"))))),
            Sp, Land, Sp, Call("iUnion", V("U")), Sp, Eq, Sp, V("univ"),
            Sp, Rightarrow, Sp, Call("HasFiniteClosedRefinement", V("p"), V("U")))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular local shrinking and extremal disconnectedness make closed restrictions open and yield finite closed subordinate refinements.",
        H("Stonean finite closed refinements"),
        Blocks(
            Paragraph(Text(
                "The universes u and v are independent. T and B carry arbitrary topologies. Regularity is required on T and extremal disconnectedness on B. "
                + "The map p is continuous, open and closed. All openness conclusions take values in the entire B. "
                + "Compactness, Hausdorffness, surjectivity and nonemptiness are absent from the general suppliers.")),
            Describe.Lean(
                DescribeId.Create("closure-domain-openness"),
                DeclarationHandle.Create(Owner + "isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected"),
                H("Openness on the closure of an open set"),
                StatementSource.FromAuthor(LocalStatement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "subtypeVal(closure(W)) is the inclusion from the subtype closure W into T, with its induced topology, and compose(p,r) means p after r. "
                        + "For a relatively open V in closure W, IsInducing.subtypeVal.isOpen_iff gives an ambient open O with V equal to the inverse image of O. "
                        + "Its image is p(O intersect closure W). At any point t of this intersection, hasBasis_opens_closure supplies an open N containing t with closure N contained in O. "
                        + "Every open neighborhood R of t meets N intersect W, because R intersect N meets W. Thus t belongs to closure(N intersect W).")),
                    Paragraph(Text(
                        "Continuity places p(t) in H = closure(p(N intersect W)). Openness of p and ExtremallyDisconnected.open_closure make H an open neighborhood in B. "
                        + "IsClosedMap.closure_image_eq_of_continuous identifies H with p(closure(N intersect W)), which is contained in p(O intersect closure W). "
                        + "These neighborhoods prove openness of every relatively open image. This local composition is repository-derived from the pinned Mathlib suppliers; "
                        + "it does not require a section or projectivity argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-closed-refinement"),
                DeclarationHandle.Create(Owner + "hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected"),
                H("Finite closed subordinate refinement"),
                StatementSource.FromAuthor(RefinementStatement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Normality is additionally required on T. The finite open cover is U : Fin n to Set T, with union all T; n may be zero. "
                        + "HasFiniteClosedRefinement is exactly the predicate in D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample. "
                        + "It asks for m : Nat, closed K : Fin m to Set T covering T and side : Fin m to Fin n, with K(j) contained in U(side(j)) and "
                        + "IsOpenMap for x in K(j) mapped to p(x.val). Empty pieces, repeated labels and restrictions that are not onto are permitted.")),
                    Paragraph(Text(
                        "Every Fin n cover is point-finite. Mathlib's exists_iUnion_eq_closure_subset supplies open W(i) covering T and closure W(i) contained in U(i). "
                        + "Take m = n, K(i) = closure W(i), and side = id. Closedness and coverage follow from closure and the open shrinking cover. "
                        + "Each restriction is open by the preceding closure-domain theorem, used on the live proof path for every piece. "
                        + "For n = 0 the premise forces T empty and the same construction uses an empty index type; no point or nonempty piece is chosen.")),
                    Paragraph(Text(
                        "For the compact Hausdorff Stonean application, B is compact Hausdorff and extremally disconnected, and T is compact Hausdorff in the same universe as B. "
                        + "Ref(B) means that every compact Hausdorff T in the same universe, every continuous open onto p : T to B, "
                        + "and every n and U : Fin n to Set T admit HasFiniteClosedRefinement p U whenever each U(j) is open and "
                        + "the pointwise cover condition holds: for every t there is j with t in U(j). This condition gives iUnion U = univ. "
                        + "Existing instances provide RegularSpace T and NormalSpace T; Continuous.isClosedMap supplies closedness from compact T and Hausdorff B. "
                        + "Apply the general finite-refinement theorem to p and U to obtain Ref(B). Onto and compactness of B "
                        + "belong to this application telescope but are unused by the stronger supplier.")),
                    Paragraph(Text(
                        "The source-owned Local.familyRegistration and Finite.familyRegistration compile with complete "
                        + "topology/map telescopes, kernel-checked equivalence bridges, actual positive laws, complete-family "
                        + "variation, sensitivity and actual observational dependence. Their Contract registrations remain "
                        + "incomplete: the scoped report records declared_unresolved for both, with IE-C050 ClosedTruthReadout, "
                        + "reason=unclassified_form, rule=source.selection_missing, and no binding certificate. The packed "
                        + "Inputs/State families do not yet supply a legal raw sourceSelection or exact structural reconstruction of "
                        + "the original Pi telescope. Topology dictionaries and proof hypotheses cannot simply become independently "
                        + "variable source coordinates, and the V or refinement-witness scopes are inside the applied IsOpenMap and "
                        + "HasFiniteClosedRefinement predicates. The missing evidence is a lawful parameter/state/readout "
                        + "correspondence and complete raw Law reconstruction with rigid universes and binder modes. This gap is "
                        + "disclosed under https://github.com/the-omega-institute/trureturing/issues/16293; neither registration is "
                        + "declared_validated.")),
                    Paragraph(Text(
                        "The pinned Mathlib shrinking and separation theorems are suppliers, and the local assembly is repository-derived. "
                        + "Library/Dynamics/gleason1958projective.md provides separate classical Stonean projectivity context; this composition is not attributed to Gleason. "
                        + "No worldwide novelty is claimed. Necessity of extremal disconnectedness, a classification of all nonmetrizable bases, and Peng's original dynamical question remain outside this result."))),
                DescribeRole.Theorem))));
}
