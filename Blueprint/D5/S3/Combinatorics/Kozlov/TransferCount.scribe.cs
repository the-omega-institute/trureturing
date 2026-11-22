using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class TransferCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/TransferCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite set of states and an admissibility test for adjacent elements give a transfer matrix. Its powers count chains of every positive length.",
        H("Counting chains with a finite transfer matrix"),
        Blocks(
            Node("ug", "uG", "Numbers of elements by state", DescribeRole.Definition,
                "Count the elements of the finite carrier with the specified state."),
            Node("tg", "TG", "Numbers of successive elements by state", DescribeRole.Definition,
                "The entry from i to j counts admissible successor elements with state j given the preceding state i."),
            Node("chaing-predicate", "ChainG", "Admissible positive-length sequences", DescribeRole.Definition,
                "Each element after the first satisfies the transition condition at the preceding element's state."),
            Node("chaing", "chainG", "The finite family of chains", DescribeRole.Definition,
                "Filter the finite family of tuples of carrier elements by the transition test."),
            Node("chaintopg", "chainTopG", "The number of chains ending at a state", DescribeRole.Definition,
                "Filter the chain family by the state of its final element and count the survivors."),
            Node("chaing-snoc-iff", "chainG_snoc_iff", "Adding a final element to a chain", DescribeRole.Theorem,
                "Retain all earlier tests and check the new transition from the previous last element."),
            Node("chaintopg-zero", "chainTopG_zero", "Single-element chains", DescribeRole.Theorem,
                "A length-one chain whose terminal state is k is exactly a carrier element in state k."),
            Node("chaintopg-succ", "chainTopG_succ", "The last-step counting recurrence", DescribeRole.Theorem,
                "Decompose a longer chain into its prefix and final element. Partition prefixes by terminal state and sum their counts times the corresponding successor multiplicities."),
            Node("chaintopg-eq", "chainTopG_eq", "State-by-state matrix powers", DescribeRole.Theorem,
                "The recurrence multiplies the previous row vector by the transition matrix. Start with the length-one count and induct on the number of transitions."),
            Node("card-chaing", "card_chainG", "Count all terminal states", DescribeRole.Theorem,
                "Partition the chains by their terminal state and sum the matrix row against the all-ones vector."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-transfer-count-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
