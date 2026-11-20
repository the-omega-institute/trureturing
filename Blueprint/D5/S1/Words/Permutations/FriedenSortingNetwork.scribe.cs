using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class FriedenSortingNetworkDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/FriedenSortingNetwork.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/frieden2026bigcactus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological restrictions of reduced reversal words.",
        H("A four-wire obstruction in a sorting network"),
        Blocks(
            Paragraph(Text("A state lists the wire labels at their current positions. The generator "
                + "with zero-based index i swaps positions i and i+1. A reduced reversal word "
                + "starts at the identity, ends at the reversal and has length n(n-1)/2. Every "
                + "unordered pair of labels crosses once, from increasing to decreasing order.")),
            Node("left_ne_right", "Distinct endpoints of a generator",
                Q(Call("left", V("i")), Neq, Call("right", V("i"))),
                "The two positions have indices i and i+1.", AssessedProvenance.FromRepo()),
            Node("restrict_cons", "Rank of a retained crossing",
                Equal(Call("restrictFrom", V("S"), V("p"), Q(V("i"), Colon, V("w"))),
                    Call("retainIfSelected", V("S"), V("p"), V("i"),
                        Add(Call("rank", V("S"), V("p"), Call("p", Call("left", V("i")))), D(1)),
                        Call("restrictFrom", V("S"), Call("step", V("p"), V("i")), V("w")))),
                "The recursive restriction always advances the full state. It prepends the stated "
                + "one-based letter precisely when both swapped labels belong to S. Rank counts "
                + "selected labels strictly to the left of the left endpoint. This is the "
                + "chronological subnetwork construction in Section 4.4.",
                AssessedProvenance.FromRepo(Source)),
            Node("rank_right_before", "Ranks of two selected adjacent wires",
                Q(Call("p", Call("left", V("i"))), InMacro, V("S"), Implies,
                    Equal(Call("rank", V("S"), V("p"), Call("p", Call("right", V("i")))),
                        Add(Call("rank", V("S"), V("p"), Call("p", Call("left", V("i")))), D(1)))),
                "The left endpoint adds exactly one selected label to the rank of the right endpoint.",
                AssessedProvenance.FromRepo()),
            Node("quartet_left", "A repeated left generator forces a forbidden restriction",
                Q(Call("ReducedReversal", V("w")), Land,
                    Call("HasRightBlock", V("n"), V("i")), Land,
                    Call("Omits", V("m"), V("i"), Add(V("i"), D(1))), Implies,
                    Q(Exists, V("S"), Comma, Call("card", V("S")), Eq, D(4), Land,
                        Call("restrict", V("w"), V("S")), InMacro, V("X"))),
                "The word w is u followed by i, m, i and v. The right block is nonempty "
                + "when i+2<n. The middle list m omits i and i+1. Between the two uses of "
                + "i, the wire at position i+1 stays fixed and the labels strictly to its "
                + "right stay in that block. The two endpoint swaps and the unique intervening "
                + "crossing in the left block yield letters 2, 1, 2. Choose one wire in the "
                + "right block. It moves only right in the retained prefix and only left in "
                + "the retained suffix. Its initial rank determines the complete restriction, "
                + "one of 123212, 232123, 321232 and 212321.", AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("frieden-network-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(params Formula[] items) => Seq(items);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
}
