using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class WisemanA261041Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/WisemanA261041.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/wiseman2019a261041");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reversible swap scan matches the two partition classes in OEIS A261041.",
        H("Wiseman A261041 and the swap scan"),
        Blocks(
            Node("partial-partition", "PartialPartition", "Partial partitions", DescribeRole.Definition,
                All("n", Nat(), Seq(Call("PartialPartition", V("n")), Sp, Colon, Sp,
                    SetBuilder(Seq(Binder("carrier", Call("Set", Fin(V("n")))), Comma, Sp,
                        Binder("blocks", Call("Setoid", V("carrier"))))))),
                "A partial partition is a dependent structure. Its carrier is an arbitrary subset of the interval and its blocks are a setoid on the subtype of points in that carrier. Position i represents the integer i+1."),
            Node("same-block", "SameBlock", "Sharing a block", DescribeRole.Definition,
                All("n", Nat(), All("p", Call("PartialPartition", V("n")), All("i", Fin(V("n")),
                    All("j", Fin(V("n")), Infix(Call("SameBlock", V("p"), V("i"), V("j")), Iff,
                        Bind(Exists, "hi", Infix(V("i"), InMacro, Field("p", "carrier")),
                            Bind(Exists, "hj", Infix(V("j"), InMacro, Field("p", "carrier")),
                                App(Field("p", "blocks"), Pair(V("i"), V("hi")), Pair(V("j"), V("hj")))))))))),
                "Both points must belong to the carrier. The setoid compares the corresponding subtype elements."),
            Node("no-consecutive", "NoConsecutive", "Adjacent positions", DescribeRole.Definition,
                All("n", Nat(), All("p", Call("PartialPartition", V("n")),
                    Infix(Call("NoConsecutive", V("p")), Iff,
                        All("i", Nat(), All("h", Infix(Add(V("i"), 1), Lt, V("n")),
                            Seq(Neg, Sp, Call("SameBlock", V("p"), Index(0), Index(1)))))))),
                "The condition forbids each consecutive pair in the ambient interval from sharing a block. Here and below, a subscript j on i denotes the finite index with value i+j and the bound inferred from h."),
            Node("triple-condition", "TripleCondition", "Consecutive triples", DescribeRole.Definition,
                All("n", Nat(), All("s", Call("Setoid", Fin(Add(V("n"), 1))),
                    Infix(Call("TripleCondition", V("s")), Iff,
                        All("i", Nat(), All("h", Infix(Add(V("i"), 2), Lt, Add(V("n"), 1)),
                            Infix(App(V("s"), Index(0), Index(2)), Implies,
                                App(V("s"), Index(0), Index(1)))))))),
                "When the endpoints of a valid consecutive triple share a block, the middle is in their block."),
            Node("left", "Left", "The partial partition class", DescribeRole.Definition,
                All("n", Nat(), Infix(Call("Left", V("n")), Eq,
                    SetBuilder(Seq(Binder("p", Call("PartialPartition", V("n"))), Sp, Mid, Sp,
                        Call("NoConsecutive", V("p")))))),
                "The carrier may be any subset, including the empty subset. This is the class counted by the OEIS entry.",
                AssessedProvenance.FromLiterature(Source)),
            Node("right", "Right", "The full partition class", DescribeRole.Definition,
                All("n", Nat(), Infix(Call("Right", V("n")), Eq,
                    SetBuilder(Seq(Binder("s", Call("Setoid", Fin(Add(V("n"), 1)))), Sp, Mid, Sp,
                        Call("TripleCondition", V("s")))))),
                "The setoid partitions all n+1 positions. The consecutive-triple implication is the condition in the OEIS comment.",
                AssessedProvenance.FromLiterature(Source)),
            Node("wiseman-bijection", "wisemanBijection", "The reversible bijection", DescribeRole.Definition,
                All("n", Nat(), Seq(Call("wisemanBijection", V("n")), Sp, Colon, Sp,
                    Infix(Call("Left", V("n")), Equiv, Call("Right", V("n"))))),
                "The value is the restriction of the composite of padding and the swap scan on full partitions. Padding adds a first point whose block contains the omitted points and the new point. Label each padded block by its least position. Starting from the identity permutation and output zero, emit the current input label under the current permutation, then compose on the right with its swap with zero. The inverse recovers each input label using the inverse current permutation before making the same update. Relabelings fixing zero commute with the scan, so the maps descend to literal partitions. Equal output endpoints with a different middle occur exactly at two successive equal nonzero input labels. The scan preserves the set of labels. The same construction has a pointwise one-block shift under the quotient cardinalities, which is retained here as explanatory refinement. The formal result below uses the reversible equivalence itself. In the formula below, restriction is the proved equivalence of the adjacent-pair and consecutive-triple conditions under the composite."),
            Paragraph(Math(Disp(BijectionBody()))),
            Node("result", "result", "The counting identity", DescribeRole.Theorem,
                All("n", Nat(), Infix(Card(Call("Left", V("n"))), Eq, Card(Call("Right", V("n"))))),
                "Taking natural cardinalities gives equality for every natural n. At zero the empty partial partition corresponds to the one-block partition of the singleton interval.",
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wiseman-a261041"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string declaration, string title, DescribeRole role,
        Formula formula, string prose, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a261041-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Field(string owner, string field) => Seq(V(owner), Dot, V(field));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Card(Formula type) => App(Seq(Operatorname, Grp(Seq(V("Nat"), Dot, V("card")))), type);
    private static Formula Infix(Formula left, Formula op, Formula right) => Seq(left, Sp, op, Sp, right);
    private static Formula Add(Formula term, byte offset) => Infix(term, Plus, D(offset));
    private static Formula Binder(string name, Formula type) => Seq(V(name), Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Open, Binder(name, type), Close, Comma, Sp, body);
    private static Formula SetBuilder(Formula body) => Seq(OpenBrace, Sp, body, Sp, CloseBrace);
    private static Formula Pair(Formula value, Formula proof) => Seq(Langle, Sp, value, Comma, Sp, proof, Rangle);
    private static Formula Index(byte offset) => Seq(V("i"), Underscore, Grp(D(offset)));
    private static Formula BijectionBody()
    {
        var index = V("n");
        var composite = Call("trans", Call("padEquiv", index), Call("partitionEquiv", index));
        var value = Call("wisemanBijection", index);
        return All("n", Nat(), Infix(value, Eq, Call("subtypeEquiv", composite, Call("restriction", index))));
    }

}
