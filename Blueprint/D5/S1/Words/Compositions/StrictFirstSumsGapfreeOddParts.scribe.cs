using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class StrictFirstSumsGapfreeOddPartsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a392707");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict zero-prepended first sums correspond to gapfree odd partitions of the same weight.",
        H("Strict First Sums and Gapfree Odd Parts"),
        Blocks(
            Paragraph(Text("The formal target is the combinatorial bridge in OEIS A392707. "
                + "Reversed partitions have their positive parts sorted increasingly. The "
                + "zero-based alternating recurrence starts at zero and is inverted by the "
                + "existing adjacent-sums function. Both combinatorial classes include the "
                + "empty partition. The A053251 mock theta coefficient identity is not "
                + "formalized here; its constant term is zero, whereas these counts start at one.")),
            Node("IsStrictFirstSums", "Strict source predicate", PredicateFormula(),
                "A positive list s is strictly increasing, and the existing firstSums "
                + "applied to zero prepended to s gives y. This strengthens the sibling's "
                + "weak predicate without redefining it or the adjacent-sums function.",
                DescribeRole.Definition),
            Node("GapfreeOdd", "Exact odd support", SupportFormula(),
                "The support equals the first k positive odd numbers. The equivalence in "
                + "the formula requires both absence of other parts and presence of every "
                + "listed part. The witness k=0 gives the empty multiset.", DescribeRole.Definition),
            Node("card_strictFirstSums_eq_gapfreeOdd", "The weight-preserving restriction", CountFormula(),
                "Reuse the frozen sibling's firstOddEquiv, its inverse and its sum theorem. "
                + "A column of height h exists exactly when row lengths drop strictly from "
                + "row h-1 to row h. Thus strict row lengths are equivalent to all positive "
                + "column heights up to the maximum occurring. The existing oddify map "
                + "takes h to 2h-1, giving exact initial odd support. Restrict the original "
                + "equivalence to this property and to total weight n, and transport via "
                + "the original list/partition equivalences. No extra hypothesis is needed.",
                DescribeRole.Theorem),
            Paragraph(Text("The sibling's auxiliaries are private in a legacy Lean module. "
                + "A local elaborator resolves their unique original constants in the "
                + "imported environment, so their definitions and proofs are reused verbatim "
                + "by reference. This is an explicit dependency on that frozen private API. "
                + "A053251 itself already states the gapfree odd interpretation and the "
                + "psi series expansion; connecting the count to that series in Lean remains "
                + "outside this module.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("a392707-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Relation(Formula symbol) => Par(Seq(V("a"), Comma, Sp, V("b"),
        Sp, Mapsto, Sp, V("a"), Sp, symbol, Sp, V("b")));
    private static Formula PredicateFormula() => Disp(All(V("y"), Call("List", Nat()), Seq(
        Call("IsStrictFirstSums", V("y")), Sp, Iff, Sp,
        Par(Seq(Exists, Sp, V("s"), Colon, Sp, Call("List", Nat()), Comma, Sp,
            Call("Pairwise", Relation(Lt), V("s")), Sp, Land, Sp,
            Par(All(V("x"), Nat(), Seq(V("x"), Sp, InMacro, Sp, V("s"), Sp, Implies, Sp,
                D(0), Sp, Lt, Sp, V("x")))), Sp, Land, Sp,
            Call("firstSums", Call("cons", D(0), V("s"))), Sp, Eq, Sp, V("y"))))));
    private static Formula SupportFormula() => Disp(All(V("m"), Call("Multiset", Nat()), Seq(
        Call("GapfreeOdd", V("m")), Sp, Iff, Sp,
        Par(Seq(Exists, Sp, V("k"), Colon, Sp, Nat(), Comma, Sp,
            All(V("x"), Nat(), Par(Seq(V("x"), Sp, InMacro, Sp, V("m"), Sp, Iff, Sp,
                Par(Seq(Exists, Sp, V("i"), Colon, Sp, Nat(), Comma, Sp,
                    V("i"), Sp, Lt, Sp, V("k"), Sp, Land, Sp,
                    V("x"), Sp, Eq, Sp, D(2), V("i"), Plus, D(1)))))))))));
    private static Formula CountFormula() => Disp(All(V("n"), Nat(), Seq(
        Count(Call("IsStrictFirstSums", Call("sort", Call("parts", V("p")), Relation(Le)))),
        Sp, Eq, Sp, Count(Call("GapfreeOdd", Call("parts", V("p")))))));
    private static Formula Count(Formula predicate) => Call("card", Call("filter",
        Par(Seq(V("p"), Sp, Mapsto, Sp, predicate)),
        Par(Seq(Call("univ"), Colon, Sp, Call("Finset", Call("Partition", V("n")))))));
}
