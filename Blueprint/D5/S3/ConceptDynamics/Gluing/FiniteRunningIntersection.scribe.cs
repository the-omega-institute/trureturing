using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class FiniteRunningIntersectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite separator computation and reconstruction on a general running-intersection tree.",
        H("Finite running-intersection computation"),
        Blocks(
            Paragraph(Text(
                "The input consists of finite node, variable and output types with their actual "
                + "enumerations and equality decisions, a decidable SimpleGraph T, decidable scopes "
                + "S n, and finite tables L n of complete assignments on S n. T is a tree and the "
                + "nodes containing each variable form a preconnected induced graph. No equality "
                + "of the original neighboring projection images is required. Empty scopes, empty "
                + "separators, empty relations and a singleton support tree are allowed.")),
            Describe.Lean(DescribeId.Create("finite-message-refinement"),
                DeclarationHandle.Create(Module + "message_table_spec"),
                H("Finite messages refine the semantic recurrence"),
                StatementSource.FromAuthor(Disp(Messages())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "FiniteJoinData abbreviates the complete telescope of message_table_spec: "
                    + "Node, Var and O with their finite enumerations and equality decisions, T "
                    + "with decidable adjacency, S with decidable membership, L, and the proof "
                    + "that T is a tree. sep d e is S e.snd intersect S e.fst; assignments are "
                    + "functions on exactly this separator with values in O. The semantic message "
                    + "is separatorMessages for the set underlying each input table. messageTable "
                    + "filters each local row against every adjacent nonparent message and then "
                    + "projects surviving rows to the separator. The genuine deleted-edge child "
                    + "component strictly decreases, proving termination for every finite degree. "
                    + "The actual output table is a subset of the original assignment carrier, "
                    + "including the single empty assignment when the separator is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-certificate-decoder"),
                DeclarationHandle.Create(Module + "decode_spec"),
                H("A finite occurrence decoder reconstructs the certificate"),
                StatementSource.FromAuthor(Disp(Decoder())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "DecodeData abbreviates the complete telescope of decode_spec, including "
                    + "the finite native carriers, graph, scopes, input tables, tree and running "
                    + "intersection proofs, an actual root, and a node list containing every node. "
                    + "A row certificate a contains one complete local row per node. Valid means "
                    + "that each row belongs to its input table and the selected rows agree on "
                    + "every complete edge separator. The selected family, rather than the original "
                    + "relations, is consistent. decode scans the supplied finite node list for "
                    + "an occurrence of each coordinate in the union and reads the corresponding "
                    + "certificate value. Existing logical tree gluing proves that all such reads "
                    + "reproduce every selected local row. The certificate consists of a root row "
                    + "and one local separator witness for each other node."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-join-solver"),
                DeclarationHandle.Create(Module + "solve_spec"),
                H("Exact root decision and a reconstructed global assignment"),
                StatementSource.FromAuthor(Disp(Solver())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "SolverData is the full telescope of solve_spec: the same finite input "
                        + "data, an actual root, complete finite node and variable lists, a complete "
                        + "output list and a base output. solve tests nonemptiness of rootTable, "
                        + "which filters the root relation against all inward tables. On acceptance "
                        + "an explicit finite function enumeration supplies candidate row families. "
                        + "Finite input-row membership and complete separator equality select a "
                        + "certificate; decode returns its common assignment on exactly the union. "
                        + "No extension, global join, or feasibility decision is assumed as an input. "
                        + "All semantic existence arguments occur in erased proofs.")),
                    Paragraph(Text(
                        "width d is separatorWidth, the maximum cardinality of an edge separator, "
                        + "with maximum zero for an empty edge set. Its power bound concerns each "
                        + "individual separator table. It is distinct from response-state boundary "
                        + "width and bounds neither the sum of table sizes, retained certificates, "
                        + "relation storage, total memory nor total running time. The finite "
                        + "certificate search need not be efficient. Arbitrary finite branching, "
                        + "empty sensitive unions, empty separators and singleton trees remain "
                        + "within the quantified statement."))),
                DescribeRole.Theorem))));

    private static Formula Messages()
    {
        var d = F.Id("d"); var e = F.Id("e"); var a = F.Id("a");
        var table = Call("messageTable", d, e);
        var sep = Call("sep", d, e);
        return All("d", F.Id("FiniteJoinData"), All("e", Call("Dart", Call("graph", d)),
            Seq(All("a", Call("Assignments", Call("output", d), sep),
                Seq(Member(a, table), Sp, Iff, Sp, Member(a, Call("separatorMessages", d, e)))),
                Sp, Land, Sp, Bound(table, Call("output", d), sep))));
    }

    private static Formula Decoder()
    {
        var d = F.Id("d"); var a = F.Id("a"); var n = F.Id("n");
        return All("d", F.Id("DecodeData"), All("a", Call("RowFamily", d),
            Seq(Call("Valid", d, a), Sp, To, Sp,
                All("n", Call("Nodes", d), Equal(
                    Call("restrict", Call("decode", d, a), Call("scope", d, n)),
                    Call("row", a, n))))));
    }

    private static Formula Solver()
    {
        var d = F.Id("d"); var j = F.Id("j"); var e = F.Id("e");
        var solved = Call("solve", d);
        var join = Call("rawJoin", d);
        var sep = Call("sep", d, e);
        return All("d", F.Id("SolverData"), Seq(
            Paren(Seq(Equal(Call("isSome", solved), Call("true")), Sp, Iff, Sp,
                Call("Nonempty", join))), Sp, Land, Sp,
            All("j", Call("Assignments", Call("output", d), Call("union", d)),
                Seq(Equal(solved, Call("some", j)), Sp, To, Sp, Member(j, join))),
            Sp, Land, Sp,
            All("e", Call("Dart", Call("graph", d)), Seq(
                Bound(Call("messageTable", d, e), Call("output", d), sep), Sp, Land, Sp,
                Call("card", sep), Sp, Le, Sp, Call("width", d)))));
    }

    private static Formula Bound(Formula table, Formula output, Formula sep) =>
        Seq(Call("card", table), Sp, Le, Sp,
            Call("power", Call("card", output), Call("card", sep)));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Paren(Seq(Forall, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body));
}
