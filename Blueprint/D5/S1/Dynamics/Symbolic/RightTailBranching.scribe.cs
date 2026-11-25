using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class RightTailBranchingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/RightTailBranching.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Branching futures and finite positive expansivity",
        H("Branching futures and finite positive expansivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-extensions-of-nonperiodic-future"),
                DeclarationHandle.Create(Owner + "finite_extensions_of_not_periodic"),
                H("Counting pasts by their last nondefault choice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a two-sided subshift, let B be the finite set of futures with at least two "
                    + "possible immediate predecessor letters. A nonperiodic right tail has at most "
                    + "1 + |B|(|A| - 1) two-sided extensions, where A is the alphabet. Distinct depths "
                    + "of the same extension cannot yield the same future, since shifting both "
                    + "futures to the prescribed tail would make that tail periodic. Choose a default "
                    + "predecessor at every realized future. Each past follows those defaults beyond "
                    + "its last nondefault choice. That choice and its future determine the entire "
                    + "past, giving the cardinal bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-finite-extensions-iff"),
                DeclarationHandle.Create(Owner + "uniform_finite_extensions_iff"),
                H("The periodic-future obstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a periodic future has a nonperiodic extension, shifting by multiples of "
                    + "the future's period gives infinitely many extensions. Periodic extensions "
                    + "of one future agree everywhere by translating both by a common period. "
                    + "Thus the same explicit bound holds for all futures exactly when every "
                    + "periodic future has only periodic extensions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bowen-bound-iff-bounded-extensions"),
                DeclarationHandle.Create(Owner + "forwardBowenBound_iff_bounded_extensions"),
                H("Bowen cardinality and the number of pasts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lemma 4.7 of Gangloff, Guillon and Oprocha identifies positive finite "
                    + "expansivity with a uniform bound on predecessor fibers. For any compatible "
                    + "metric, closeness at every nonnegative time forces equality of every "
                    + "nonnegative coordinate at a sufficiently small scale. Conversely, shifting "
                    + "a future fiber forward by the radius of a sufficiently large window embeds "
                    + "it in a single strict forward Bowen ball."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-positive-expansivity-iff"),
                DeclarationHandle.Create(Owner + "finitelyPositiveExpansive_iff_periodic_extensions"),
                H("Finite positive expansivity with finitely many branching futures"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With finitely many branching futures, finite positive expansivity is "
                    + "equivalent to every periodic future having only periodic extensions. "
                    + "The counting argument applies to the full two-sided subshift and every "
                    + "compatible metric."))),
                DescribeRole.Theorem))));
}
