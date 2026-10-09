using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageBoundEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equality characterization is Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475. A graph is star-like precisely when every vertex is a leaf or a stem having one or two leaf neighbours.",
        H("Equality Graphs for the Two-Thirds Bound"),
        Blocks(
            Node("residual-total-lt-of-core-nonempty", "residual_total_lt_of_core_nonempty", "Strictness outside stem blocks", "If an isolate-free graph has a vertex in no stem block, the residual critical-incidence estimate is strict.", DescribeRole.Theorem),
            Node("active-block-total-lt-of-large-stem", "active_block_total_lt_of_large_stem", "Strictness for three leaves", "If a stem has at least three leaf neighbours, the active-block critical-incidence estimate is strict.", DescribeRole.Theorem),
            Node("critical-total-eq-of-avd-eq", "critical_total_eq_of_avd_eq", "Equality of incidence counts", "Equality in the two-thirds average bound gives equality of the total critical and omitted incidence counts.", DescribeRole.Theorem),
            Node("starlike-of-avd-eq-two-thirds", "starLike_of_avd_eq_two_thirds", "Equality forces a star-like graph", "An isolate-free graph attaining average 2|V(G)|/3 is star-like. A vertex outside all stem blocks or a stem with three leaves would give a strict incidence inequality.", DescribeRole.Theorem),
            Node("avd-eq-two-thirds-of-starlike", "avd_eq_two_thirds_of_starLike", "Star-like graphs attain equality", "Every finite star-like graph without isolated vertices has dominating-set average equal to two thirds of its order.", DescribeRole.Theorem),
            Node("avd-eq-two-thirds-iff-starlike", "avd_eq_two_thirds_iff_starLike", "Beaton–Cameron equality characterization", "For a finite graph without isolated vertices, the average cardinality of dominating sets equals two thirds of the graph order if and only if every vertex is a leaf or a stem with one or two leaf neighbours.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
