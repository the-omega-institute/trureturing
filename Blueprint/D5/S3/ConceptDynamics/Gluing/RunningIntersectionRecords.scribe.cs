using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class RunningIntersectionRecordsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Running intersection identifies full cut boundaries and lets every specified local row "
            + "extend to a raw global record on a finite tree.",
        H("Running Intersection Records"),
        Blocks(
            Paragraph(Text(
                "Node indexes scopes S and local relations Gamma. Variables and their dependent "
                    + "value types are arbitrary; scopes and relations may be infinite. An assignment "
                    + "on U_A supplies precisely the variables occurring in A. J_A is the raw join "
                    + "requiring each node restriction to belong to its local relation. The empty "
                    + "join is the singleton canonical empty assignment. These are the existing "
                    + "HistoryPayloadFactorization assignment and join definitions.")),
            Entry("RunningIntersection", "occurrence-connectivity", "Connected occurrences",
                Seq(Call("RI", F.Id("T"), F.Id("S")), Sp, Iff, Sp,
                    Forall, Sp, F.Id("x"), Comma, Sp,
                    Call("Preconnected", Call("induce", F.Id("T"), Call("Occ", F.Id("x"))))),
                "RI requires each occurrence-induced graph to be preconnected. When a variable "
                    + "occurs, this is connectedness; absent variables impose no condition. In an "
                    + "acyclic graph, the unique ambient path between two occurrences stays within "
                    + "their occurrence set.", DescribeRole.Definition),
            Entry("edgeLeft", "deleted-edge-component", "An actual deleted-edge component",
                Equal(Call("L", F.Id("e")), Call("ReachableSet",
                    Call("deleteEdges", F.Id("T"), Call("singleton", Call("edge", F.Id("e")))),
                    Call("fst", F.Id("e")))),
                "L is defined by reachability from the first endpoint after deleting the chosen "
                    + "edge. Its complementary set is R.", DescribeRole.Definition),
            Entry("edge_cut_components", "two-cut-components", "Exactly two endpoint components",
                Seq(Call("IsTree", F.Id("T")), Sp, To, Sp,
                    Equal(Call("complement", Call("L", F.Id("e"))),
                        Call("ReachableSet", Call("deleteEdges", F.Id("T"),
                            Call("singleton", Call("edge", F.Id("e")))), Call("snd", F.Id("e"))))),
                "The first endpoint belongs to L and the second does not. Every connected "
                    + "component of the deleted graph is one of the two endpoint components. "
                    + "This topology requires the tree hypothesis and requires no RI."),
            Entry("boundary_eq_union_separators", "full-boundary-union", "The full boundary of any region",
                Seq(Call("RI", F.Id("T"), F.Id("S")), Sp, To, Sp,
                    Equal(Call("intersection", Call("U", F.Id("A")),
                        Call("U", Call("complement", F.Id("A")))),
                        Call("unionCrossingSeparators", F.Id("T"), F.Id("S"), F.Id("A")))),
                "For arbitrary A, its full overlap with the complement is the union of S_p "
                    + "intersect S_q over edges with p in A and q outside A. An occurrence walk "
                    + "crosses the inverse image of A inside the occurrence-induced graph. No "
                    + "tree or finiteness assumption is needed. The boundary value is one "
                    + "dependent assignment on this entire union, including when the complement "
                    + "is disconnected; complete complement records already agree on shared variables."),
            Entry("cut_scope_eq_separator", "full-cut-separator", "A cut overlap equals its separator",
                Seq(Call("IsTree", F.Id("T")), Sp, Land, Sp,
                    Call("RI", F.Id("T"), F.Id("S")), Sp, To, Sp,
                    Equal(Call("intersection", Call("U", Call("L", F.Id("e"))),
                        Call("U", Call("complement", Call("L", F.Id("e"))))),
                        Call("intersection", Call("S", Call("fst", F.Id("e"))),
                            Call("S", Call("snd", F.Id("e")))))),
                "Only the deleted edge crosses its two components. RI therefore identifies "
                    + "the complete component overlap with the complete edge separator."),
            Entry("cut_records_glue_unique", "fixed-record-gluing", "Unique gluing of two fixed records",
                Seq(Exists, Bang, Sp, F.Id("j"), Colon, Sp, F.Id("J"), Comma, Sp,
                    Equal(Call("restrict", F.Id("j"), F.Id("L")), F.Id("a")), Sp, Land, Sp,
                    Equal(Call("restrict", F.Id("j"), F.Id("R")), F.Id("b"))),
                "Given a complete record a on L and b on R whose edge-separator restrictions "
                    + "agree, there is exactly one raw global record with those two restrictions. "
                    + "The tree and RI assumptions justify replacing full overlap by the edge "
                    + "separator. Full-overlap gluing itself requires neither assumption, and "
                    + "local relations may be empty. This is uniqueness for fixed a and b."),
            Entry("EdgeProjectionConsistency", "complete-edge-images", "Equality of complete projection images",
                Seq(Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Comma, Sp,
                    Call("Adj", F.Id("T"), F.Id("p"), F.Id("q")), Sp, To, Sp,
                    Equal(Call("project", Call("Gamma", F.Id("p")), Call("C", F.Id("p"), F.Id("q"))),
                        Call("project", Call("Gamma", F.Id("q")), Call("C", F.Id("p"), F.Id("q"))))),
                "C_pq is S_p intersect S_q. Both images are sets of complete dependent "
                    + "assignments on C_pq; equality matches whole separator records.", DescribeRole.Definition),
            Entry("extend_record_at_neighbor", "one-neighbor-extension", "Preserve a whole partial record",
                Seq(Forall, Sp, F.Id("a"), Colon, Sp, Call("J", F.Id("A")), Comma, Sp,
                    Exists, Sp, F.Id("b"), Colon, Sp, Call("J", Call("union", F.Id("A"),
                        Call("singleton", F.Id("q")))), Comma, Sp,
                    Equal(Call("restrict", F.Id("b"), Call("U", F.Id("A"))), F.Id("a"))),
                "Assume a tree, RI, complete edge projection consistency, a connected induced "
                    + "region A, and an edge from p in A to q outside A. The restriction of a "
                    + "to S_p supplies a matching Gamma_q row. The overlap U_A intersect S_q "
                    + "equals C_pq. Gluing on the node set A union {q} preserves every previous "
                    + "coordinate and uses no records outside that set."),
            Entry("local_row_extends_raw_join", "every-row-extension", "Every specified row extends",
                Seq(Forall, Sp, F.Id("r"), Comma, Sp, F.Id("a"), Sp, InMacro, Sp,
                    Call("Gamma", F.Id("r")), Comma, Sp, Exists, Sp, F.Id("j"), Colon, Sp,
                    F.Id("J"), Comma, Sp, Equal(Call("restrict", F.Id("j"), Call("S", F.Id("r"))),
                        F.Id("a"))),
                "Assume finite Node, a tree, RI, nonempty local relations and equality of "
                    + "complete edge projection images. Tree connectedness supplies nonempty Node. "
                    + "Starting with the specified row, each growth step preserves the entire "
                    + "previous assignment and reduces the finite complement until all nodes "
                    + "are included. Global extension is existential and need not be unique. "
                    + "For any additional constraint K, actual worlds are W = J intersect K; "
                    + "raw extension does not assert W is nonempty."))));

    private static DocumentBlock Entry(string declaration, string id, string title,
        Formula formula, string explanation, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
