using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class ExecutableCapacityJoinDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Observer/Separation/ExecutableCapacityJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite separator computation decides every original fixed-tree active peak budget.",
        H("Executable capacity-sensitive tree gluing"),
        Blocks(
            Paragraph(Text(
                "I is finite, each coordinate alphabet X i is finite and nonempty, D is a "
                + "nonempty promise subset of the full coordinate product and f maps D into the "
                + "finite output alphabet O. The original implementation tree t is Full and its "
                + "root contains every coordinate. Its constructor allows arbitrary finite "
                + "branching, unary vertices and zero-child constant vertices. Nodes t is the "
                + "entire original node carrier, including the root. A separate decidable "
                + "SimpleGraph G on this carrier is a tree whose actual capacity-sensitive "
                + "supports satisfy running intersection. G is not identified with t.")),
            Describe.Lean(DescribeId.Create("original-capacity-separator-solver"),
                DeclarationHandle.Create(Module + "source_solver_spec"),
                H("Exact original-task solver with a finite global witness"),
                StatementSource.FromAuthor(Disp(SourceStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "SourceData abbreviates the full telescope of source_solver_spec: I, V, "
                        + "O, X, finite enumerations and equality decisions for the input and output "
                        + "alphabets, nonempty coordinate alphabets, t, Full t, full root support, "
                        + "D with decidable membership, its nonemptiness proof, f, a finite "
                        + "enumeration and equality on the actual Nodes t, G with decidable "
                        + "adjacency, its tree and original-sensitive-support running intersection "
                        + "proofs, a root of G, complete finite node and illegal-cell lists, and "
                        + "a complete finite output list. These are finite presentations of the "
                        + "original inputs; no extension or feasibility oracle is supplied.")),
                    Paragraph(Text(
                        "costTable computes leaf coordinates structurally, fills legal cells "
                        + "using f and illegal cells using the supplied assignment h, enumerates "
                        + "all promised inputs, and counts distinct full complementary response "
                        + "functions. Complementary inputs range over their entire original "
                        + "product. Thus it counts precisely active capacity, rather than the "
                        + "capacity of all possible prefixes. The first equality identifies this "
                        + "finite table with CapacitySensitiveSupport.sourceCost on every original "
                        + "node and every illegal-cell assignment. This equality transports "
                        + "cardinality between the finite image of response functions and the "
                        + "subtype of the same reached responses; it preserves the original "
                        + "response count.")),
                    Paragraph(Text(
                        "Finite pairs of assignments decide sensitive coordinates. localTable "
                        + "then enumerates local rows and checks the original universal-extension "
                        + "condition against all finite illegal-cell assignments. Its underlying "
                        + "set is exactly localFeasible for the computed cost. sourceSolve feeds "
                        + "these input-derived tables into the terminating general separator "
                        + "recurrence. A base value is read from the finite output list, whose "
                        + "nonemptiness follows from D and f. It does not select a desired extension.")),
                    Paragraph(Text(
                        "For every natural budget k, sourceSolve returns Some exactly when the "
                        + "minimum actually reachable original-node peak is at most k. This uses "
                        + "CapacitySensitiveSupport.source_result for the same t, D and f. Every "
                        + "returned assignment belongs to the natural join on the exact union of "
                        + "sensitive supports. Each inward finite message equals the existing "
                        + "semantic separatorMessages relation and has at most card O raised to "
                        + "the separator cardinality entries. The last inequality places that "
                        + "cardinality below the actual support-separator width.")),
                    Paragraph(Text(
                        "Empty coordinate products, zero-child constant roots, singleton "
                        + "alphabets, empty sensitive unions, empty separators and singleton "
                        + "support trees are included. The original nonempty promise and f already "
                        + "force a nonempty output alphabet. Separator width counts illegal-cell "
                        + "assignments for gluing constraints; response-state boundary width "
                        + "counts states in one observation process. No bound on total runtime, "
                        + "the sum of table sizes, total storage or certificate storage follows "
                        + "from a single separator-table bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("empty-coordinate-root-check"),
                DeclarationHandle.Create(Module + "result"),
                H("The empty-coordinate constant root has peak one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Equal(Call("answer", D(0)), Call("false")), Sp, Land, Sp,
                    Equal(Call("answer", D(1)), Call("true")), Sp, Land, Sp,
                    Equal(Call("minimumPeak", Call("emptyTree"), Call("emptyPromise"),
                        Call("constantTask")), D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here emptyTree is the actual zero-child implementation root on Empty "
                    + "coordinates, emptyPromise is the nonempty singleton empty product, and "
                    + "constantTask has output Unit. The separate support graph is the singleton "
                    + "tree. answer is the executable sourceSolve success flag for these exact "
                    + "inputs. Kernel evaluation gives false at zero and true at one; the general "
                    + "source_solver_spec then identifies the original counted-root minimum "
                    + "peak as one, as already given by the original constant-task model. "
                    + "The computation includes no illegal cells or separators."))),
                DescribeRole.Theorem))));

    private static Formula SourceStatement()
    {
        var d = F.Id("d"); var k = F.Id("k"); var j = F.Id("j");
        var e = F.Id("e"); var a = F.Id("a");
        var computed = Call("sourceSolve", d, k);
        var table = Call("messageTable", d, k, e);
        var sep = Call("separator", d, e);
        return All("d", F.Id("SourceData"), Seq(
            Equal(Call("costTable", d), Call("sourceCost", d)), Sp, Land, Sp,
            All("k", F.Id("Nat"), Seq(Equal(Call("isSome", computed), Call("true")), Sp, Iff, Sp,
                Call("minimumPeak", d), Sp, Le, Sp, k)), Sp, Land, Sp,
            All("k", F.Id("Nat"), All("j", Call("UnionAssignment", d),
                Seq(Equal(computed, Call("some", j)), Sp, To, Sp,
                    Member(j, Call("rawJoin", d, k))))), Sp, Land, Sp,
            All("k", F.Id("Nat"), All("e", Call("Dart", Call("supportGraph", d)), Seq(
                All("a", Call("SeparatorAssignment", d, e), Seq(Member(a, table), Sp,
                    Iff, Sp, Member(a, Call("separatorMessages", d, k, e)))), Sp, Land, Sp,
                Call("card", table), Sp, Le, Sp,
                Call("power", Call("card", Call("output", d)), Call("card", sep)),
                Sp, Land, Sp, Call("card", sep), Sp, Le, Sp, Call("separatorWidth", d))))));
    }

    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Paren(Seq(Forall, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body));
}
