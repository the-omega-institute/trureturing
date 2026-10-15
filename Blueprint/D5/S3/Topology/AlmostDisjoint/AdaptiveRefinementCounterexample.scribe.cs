using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class AdaptiveRefinementCounterexampleDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula P => Call("projection", V("A"), V("natValue"), V("ell"));
    private static Formula Statement => Disp(Seq(
        Ex("A", Call("Set", Call("Set", V("Nat")))),
        Ex("ell", Fn(V("A"), V("unitInterval"))),
        Call("ADFamily", V("A")), Sp, Land, Sp,
        Grp(Seq(All("a", V("A")), Call("ConvergesOn", V("natValue"), Call("val", V("a")), Call("ell", V("a"))))),
        Sp, Land, Sp, Call("IsClosed", Call("literalSpace", V("A"), V("natValue"), V("ell"))),
        Sp, Land, Sp, Call("IsCompact", Call("literalSpace", V("A"), V("natValue"), V("ell"))),
        Sp, Land, Sp, Call("Continuous", P), Sp, Land, Sp, Call("IsOpenMap", P),
        Sp, Land, Sp, Call("Surjective", P), Sp, Land, Sp,
        Grp(Seq(All("b", V("Bool")), Call("IsOpen", Call("U", V("b"))))),
        Sp, Land, Sp, Grp(Seq(All("x", Call("Space", V("A"), V("natValue"), V("ell"))),
            Ex("b", V("Bool")), V("x"), Sp, InMacro, Sp, Call("U", V("b")))),
        Sp, Land, Sp, Neg, Call("HasFiniteClosedRefinement", P, V("U")),
        Sp, Land, Sp, Neg, Call("HasOpenZeroDimensionalResolution", P)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal compact open surjection defeats all finite closed open-restriction refinements.",
        H("An adaptive finite-refinement counterexample over the convergent sequence"),
        Blocks(
            Paragraph(Text("The total space is the literal tagged subset of OnePoint Nat times unitInterval times Bool^(A + Nat) supplied by TaggedCompactSpace. Write g for its real value coordinate. U(false) is the literal set g < 2/3, and U(true) is the literal set g > 1/3. These two open sets cover the total space. A finite refinement may have any number of closed pieces, including zero when the total space is empty; its assignments into the original cover may repeat, pieces may be empty, and no individual restriction must be onto. Every restriction is required to be open into the entire base OnePoint Nat.")),
            Paragraph(Text("The information audit remains unfinished. The source-owner mirror checks the whole existential source statement, but whole-source variation and raw occurrence reconstruction/sourceSelection remain absent under https://github.com/the-omega-institute/trureturing/issues/16293. No validated four-slot registration is asserted.")),
            Describe.Lean(
                DescribeId.Create("exists-compact-open-map-no-finite-closed-refinement"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample.exists_compact_open_map_no_finite_closed_refinement"),
                H("Closed open-restriction pieces would create a forbidden threshold partitioner"),
                StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the actual convergent maximal almost-disjoint family from ThresholdPartitionerElimination, index it by its set of distinct members, and choose an existing branch representative for each member to define its limit. The no-threshold-partitioner theorem is unconditional: neither CH nor regularity of continuum is assumed. The compact construction gives the actual continuous open onto projection and continuous compact sections with clopen ranges.")),
                    Paragraph(Text("For a closed piece K whose projection is open into the entire base, intersect K with each clopen section range. The projection of this intersection is both compact and open in OnePoint Nat. If it contains infinity it contains cofinitely many natural numbers; otherwise compactness makes its natural-number part finite. On each actual family member, the section over n equals the actual natural point d_n. Hence the set of n with d_n in K partitions every family member.")),
                    Paragraph(Text("A finite union of partitioners is again a partitioner. Group all refinement pieces assigned to U(false). The union of their natural-point sets contains every n with natValue(n) <= 1/3: a piece assigned to U(true) cannot cover such a point. The union is contained in natValue(n) < 2/3 by subordination. This produces the exact threshold partitioner that the supplier excludes, contradicting every finite closed refinement.")),
                    Paragraph(Text("If a compact Hausdorff zero-dimensional space Z mapped continuously onto the total space with open composite projection, pull the two open sets back to Z. Mathlib supplies a finite subordinate disjoint clopen cover. Its images are closed and cover the total space. For each image, IsOpenMap.of_comp transfers openness of the composite restriction along the continuous surjection from the clopen cell onto that image. These images would be a forbidden refinement. No metrizability of Z is required.")),
                    Paragraph(Text("The result establishes the actual compact-open-map obstruction over OnePoint Nat and excludes an open zero-dimensional resolution for that map. The extension to every infinite compact zero-dimensional metrizable base, the full base classification, and the original Peng dynamical question require their separate proofs. Worldwide novelty is not established by this formalization."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination"))]));
}
