using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class CompleteBlockResponsesDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses.";

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        string title,
        string text,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Owner + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite-horizon legality response classes and their field-valued response matrix.",
        H("KBonacci Complete Block Responses"),
        Blocks(
            Entry(
                "complete-block-run",
                "run",
                "Totalized scanner execution",
                "The original partial k-tail scanner is totalized by retaining an optional live tail; "
                + "a rejected execution is represented by none and remains absorbing.",
                DescribeRole.Definition),
            Entry(
                "complete-block-response",
                "response",
                "Legality response",
                "The response records exactly whether the totalized execution remains live after a literal "
                + "bit word. It exposes success versus rejection without adding a clock or source model.",
                DescribeRole.Definition),
            Entry(
                "complete-block-bit-equivalence",
                "BitEquivalent",
                "Bounded bit-response equivalence",
                "Two optional scanner states are equivalent at horizon h when every literal word of length "
                + "at most h has the same legality response.",
                DescribeRole.Definition),
            Entry(
                "complete-block-word",
                "blockWord",
                "Literal concatenation of complete blocks",
                "A list of width-m blocks is flattened in chronological order into its actual Boolean word.",
                DescribeRole.Definition),
            Entry(
                "complete-block-equivalence",
                "BlockEquivalent",
                "Bounded complete-block equivalence",
                "Two optional scanner states are equivalent when every list of at most H literal width-m "
                + "blocks has the same endpoint legality response.",
                DescribeRole.Definition),
            Entry(
                "complete-block-live-response-classes",
                "live_response_classes",
                "Live response classes",
                "For live tails, bounded legality responses agree exactly when the remaining-one coordinates "
                + "truncated at h agree. The proof uses the actual scanner responses, including the all-one "
                + "separating word; it does not claim a physical source realization.",
                DescribeRole.Theorem),
            Entry(
                "complete-block-budget-conversion",
                "complete_block_budget",
                "Complete blocks exactly encode the bounded bit horizon",
                "For arbitrary widths and horizons, the complete-block relation is equivalent to the bit "
                + "relation at horizon H*m. Short words are zero-padded because the scanner's zero transition "
                + "preserves its legality response.",
                DescribeRole.Theorem),
            Entry(
                "complete-block-representative",
                "representative",
                "Canonical live-class representative",
                "Each truncated remaining-one coordinate is represented by the corresponding live scanner "
                + "tail, giving one canonical state for every possible live response class.",
                DescribeRole.Definition),
            Entry(
                "complete-block-bit-test",
                "BitTest",
                "Finite dependent family of bounded tests",
                "A bit test stores a word length below h+1 together with its literal Boolean word.",
                DescribeRole.Definition),
            Entry(
                "complete-block-row",
                "row",
                "Complete Boolean response row",
                "The row of a totalized scanner state records its legality response on every bounded literal "
                + "word, retaining all tests rather than selecting a probe family.",
                DescribeRole.Definition),
            Entry(
                "complete-block-live-class-count",
                "live_class_count",
                "Exact number of live Boolean rows",
                "The range of live response rows has cardinality min k (h+1). The representative family is "
                + "injective and every live tail has one of those rows.",
                DescribeRole.Theorem),
            Entry(
                "complete-block-total-class-count",
                "total_class_count",
                "Exact number of totalized response rows",
                "Adding the absorbing rejection state contributes one row disjoint from the live rows, so "
                + "the total row count is min k (h+1)+1.",
                DescribeRole.Theorem),
            Entry(
                "complete-block-response-matrix",
                "responseMatrix",
                "Field-valued response matrix",
                "Over any field, the Boolean response rows are interpreted as zero-one matrix entries with "
                + "optional scanner states as rows and all bounded literal tests as columns.",
                DescribeRole.Definition),
            Entry(
                "complete-block-bit-response-rank",
                "bit_response_rank",
                "Response rank equals the live class count",
                "Over every field, the response matrix has rank min k (h+1). A lower-triangular all-one-word "
                + "minor supplies the lower bound, while the coordinate factorization supplies the upper bound. "
                + "This is the formal response-matrix result; the wider physical Proposition 3.3 remains open "
                + "where it requires an additional source-history or acquisition bridge.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "These declarations concern the totalized forbidden-1^k legality observation of the actual "
                + "scanner. They establish the finite-horizon response classes, complete-block budget conversion, "
                + "and field-valued response rank. They do not by themselves identify an arbitrary physical source "
                + "history, a probability law, or a minimal autonomous quotient.")))));
}
