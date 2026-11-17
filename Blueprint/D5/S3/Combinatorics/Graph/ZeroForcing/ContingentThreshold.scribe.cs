using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class ContingentThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/ContingentThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite simple graph, a placement survives every fixed set of at most k edge faults exactly when every nonempty disjoint white set has more than k unique-neighbour outside vertices.",
        H("Fixed edge faults and the unique-neighbour boundary"),
        Blocks(
            Paragraph(Text("This is equation (2.2) of Theorem 2.1 in Contingent zero forcing at fixed cycle rank. The other assertions of that theorem, including bounded enlargement, optimum placement and the recurrence, are outside this result. The graph need not be connected or nonempty, and k ranges over all natural numbers. The source's connected nonempty graph and positive integer budget specialize this stronger domain directly. For a source set S, use its finite enumeration S.toFinset and classical decidable equality and adjacency. Finite Set.toFinset membership is exactly set membership; the same conversion applies to W and to each fault set F. Finite simple undirected edges are unordered pairs Sym2 V. No vertices are deleted or relabelled.")),
            Def("legal-force", "LegalForce", "A legal blue-source force",
                "A source belongs to the current blue set, its target is outside that set and adjacent, and all its other neighbours are blue. This refines the existing Black.force constructor with an explicit white target; it introduces no alternative closure semantics."),
            Def("legal-run", "LegalRun", "A finite chronological run",
                "The empty list leaves the set unchanged. Each list head is a legal force and inserts exactly its target before the remaining run. The terminal set is part of the relation, so a successful list ends at the full vertex set."),
            Thm("chronology", "chronological_iff_zero_forcing", "Finite chronology equals the original inductive closure",
                "Soundness substitutes derivations with the original Black.bind and Black.force. Completeness inducts on the number of white vertices. If any vertex is missing, Black.exists_initial_force provides a legal first move. Black.mono preserves full eventual closure after inserting its target, and the white cardinal strictly decreases. The recursive lists are concatenated by the LegalRun.cons constructor. This finite exhaustion construction supplies the chronological witnesses used in both directions of the fault theorem."),
            Def("boundary", "boundary", "The unique-neighbour boundary",
                "The boundary consists of outside vertices whose finiteNeighbors intersection with W has cardinality one. Its cardinality is the source statistic b_G(W). Both finiteNeighbors and IsFort are the original public generalized-Petersen suppliers with arbitrary finite graph parameters."),
            Def("critical-edges", "criticalEdges", "The exact critical crossing edges",
                "For each boundary vertex choose its unique neighbour in W and form their unordered edge. The image is injective: equality with endpoints unswapped identifies outside vertices; swapped equality would put an outside vertex inside W."),
            Thm("critical-minimum", "critical_edges_fort_minimality", "The exact minimum deletion for a fixed white set",
                "For nonempty W the critical edges belong to the original graph, their number is the boundary cardinality, and deleting exactly them makes W an ordinary fort. An outside vertex with originally zero neighbours retains zero; one with one loses its unique crossing edge; one with at least two loses no crossing edge, because it is not a boundary vertex. Every fault set that makes W a fort must contain these critical edges, yielding the required cardinal lower bound. This containment statement does not assert that arbitrary larger deletion sets preserve a fort."),
            Def("contingent", "Contingent", "Fixed faults and fault-dependent runs",
                "For every finite set F of original edges with cardinality at most k, there exists a legal chronological run in G.deleteEdges F starting from exactly S and ending at all vertices. S is chosen before F. The list may depend on F, and the deleted graph stays fixed throughout the list. There is no bound k≤number of vertices or edges, no shared list across faults, and no connectedness requirement on the deleted graph."),
            Def("lambda", "lambda", "The obstruction minimum in extended natural numbers",
                "Take the infimum of boundary cardinalities over all nonempty finite W disjoint from S. The value is in ENat, so an empty obstruction family has value infinity. In particular S equal to all vertices has lambda equal to infinity and succeeds with the empty list for every finite budget, including zero. The empty vertex type is included with the same convention."),
            Thm("threshold", "contingent_iff_lambda_gt", "The fixed-fault threshold, equation (2.2)",
                "If a disjoint nonempty W has boundary size at most k, delete its exact critical edges. Chronological soundness converts any purported successful list to the original Black closure, contradicting IsFort.not_black_of_disjoint. Conversely, when a fault set defeats the original closure, its nonblack complement is a nonempty fort disjoint from S: a unique remaining white neighbour could be forced by an already black source. Every critical edge of that complement must be in the actual fault set, so its original boundary size is at most the fault budget. The boundary threshold rules this out; chronological completeness then supplies a list for this particular fault set. An attained ENat infimum handles nonempty obstruction families, and the empty family uses infinity. This equivalence does not establish bounded enlargement, optimum placement or the recurrence in Theorem 2.1."))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("contingent-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Thm(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("contingent-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
