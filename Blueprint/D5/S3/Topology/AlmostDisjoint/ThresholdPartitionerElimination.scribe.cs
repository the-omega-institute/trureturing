using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class ThresholdPartitionerEliminationDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Statement => Disp(Seq(
        Ex("N", Fn(V("Branch"), Call("Set", V("Nat")))),
        Grp(Seq(All("x", V("Branch")), Call("natBranch", V("x")), Sp, Subseteq, Sp, Call("N", V("x")))),
        Sp, Land, Sp, Call("MADFamily", Call("range", V("N"))), Sp, Land, Sp,
        Grp(Seq(All("x", V("Branch")), Call("ConvergesOn", V("natValue"), Call("N", V("x")), Call("limitValue", V("x"))))),
        Sp, Land, Sp, Grp(Seq(All("r", V("unitInterval")), All("V", Call("Set", V("unitInterval"))),
            V("V"), Sp, InMacro, Sp, Call("nhds", V("r")), Sp, Rightarrow, Sp,
            Neg, Call("InFiniteUnionIdeal", V("N"), Call("preimage", V("natValue"), V("V"))))),
        Sp, Land, Sp, Neg, Grp(Seq(Ex("D", Call("Set", V("Nat"))),
            Call("Partitions", V("N"), V("D")), Sp, Land, Sp, V("L"), Sp, Subseteq, Sp, V("D"),
            Sp, Land, Sp, V("D"), Sp, Subseteq, Sp, V("U")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-limit pairing eliminates actual threshold partitioners without regularity of continuum.",
        H("A convergent maximal family with no threshold partitioner"),
        Blocks(
            Paragraph(Text("Information audit is unfinished. The mirrored attempt retains the complete source certificate and actual family variation, but raw source reconstruction/sourceSelection is absent. The concrete gap is disclosed in https://github.com/the-omega-institute/trureturing/issues/16293. No validated four-slot status is asserted.")),
            Paragraph(Text("L is the literal set of natural numbers n with real natValue(n) <= 1/3; U is the literal set with real natValue(n) < 2/3. Partitions(N,D) means that each actual N(x) is almost contained in D or almost disjoint from D. The final almost-disjoint family is range N. Paired labels can name the same member; the theorem does not assert finite intersections for all distinct labels.")),
            Describe.Lean(
                DescribeId.Create("exists-mad-no-threshold-partitioner"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination.exists_mad_no_threshold_partitioner"),
                H("Every literal threshold separator is defeated by its own paired stage"),
                StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Start with the branch-labeled convergent unrestricted MAD family whose value neighborhoods escape its finite-union ideal. Every actual threshold partitioner has a common value supported by both colors. The exact branch color-fiber theorem gives continuum many labels of each color at that value. The set of all actual partitioners has cardinal at most continuum and is indexed by its initial ordinal.")),
                    Paragraph(Text("At every stage, the set of previously chosen endpoints has cardinal below continuum: an initial segment is smaller than its initial ordinal cardinal, and its product with Bool remains smaller than continuum. A well-founded recursion selects one fresh endpoint of each opposite color. This uses neither CH nor regularity of continuum, including when continuum is singular.")),
                    Paragraph(Text("The injective endpoint map defines an involution that swaps selected endpoints and fixes unused labels. Both endpoints share their actual limit. Replace M(x) by M(x) union M(mate(x)). Distinct actual merged members have four finite old intersections; every old member lies in a merged member, so unrestricted maximality transfers. The original finite_sUnion_converges supplier proves convergence. Finite union generators produce exactly the same ideal before and after pairing, preserving the no-small-neighborhood clause.")),
                    Paragraph(Text("Any final partitioner partitions each old member by containment, hence is one of the enumerated old threshold partitioners. At its own stage, a merged infinite member contains an infinite almost-in part and an infinite almost-out part. Both its intersection and difference with that partitioner are infinite, a contradiction. This is the separator-elimination ingredient for the literal compact tagged-product construction. The compact counterexample, finite-refinement obstruction, base classification, and original Peng dynamical question still require their separate proofs."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/BranchColorFiber"))]));
}
