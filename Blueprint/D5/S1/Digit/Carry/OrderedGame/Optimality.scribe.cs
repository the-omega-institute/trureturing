using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry.OrderedGame;

internal sealed class OptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete raw weighted terminal domination and the ordered terminality bridge.",
        H("Raw Greedy Optimality for the Ordered Zeckendorf Game"),
        Blocks(
            Paragraph(Text("All indices here are raw, zero-based indices. Raw reward includes "
                + "the carry and all sorting switches paid by that carry. The concrete G is the "
                + "existing greedy recursion, not a supremum or a maximum over competing paths.")),
            Describe.Lean(DescribeId.Create("ordered-game-singleton-merge-cascade"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Optimality.singleton_merge_cascade"),
                H("Finite singleton merge cascade"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive-index singleton merge followed by the finite "
                    + "high cascade yields a binary upper tail, preserves lower coordinates, "
                    + "and replays with the same reward under arbitrary lower-boundary changes. "
                    + "The lower input must remain positive; higher coordinates agree."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-lower-split-merge-exchange"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Optimality.lower_split_merge_exchange"),
                H("Extract a lower split across a finite high cascade"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After the actual high cascade, the lower nonzero split "
                    + "is again preferred with its original reward. Taking it first permits "
                    + "legal replay to the same endpoint, including j=a-1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-binary-separated-merge-exchange"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Optimality.binary_separated_merge_exchange"),
                H("Exchange separated merge blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a binary state, a competing merge at b at least a+3 "
                    + "completes its actual high cascade before the least merge a. Replaying "
                    + "the high block after a is legal with equal reward and a common endpoint, "
                    + "including b=a+3 where the coordinate below the block changes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-raw-terminal-bound"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Optimality.raw_terminal_bound"),
                H("Every complete legal raw path is bounded by G"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every RawPath c e w with CanonicalRaw e, w is at "
                    + "most G c. There is no restriction on the raw start, spectator multiplicities "
                    + "or interleaving of merges and splits. Strict carry-measure induction first "
                    + "establishes every one-step comparison at c. Ones use terminal promotion; "
                    + "nonzero split competitors use the actual split-prefix cut before merges "
                    + "are considered. Shared-input repairs and the singleton exchanges settle "
                    + "the remaining merges. Binary states use an inner strong induction on the "
                    + "competing merge index. Every use of terminal optimality is at a strict "
                    + "successor, and every equality for G follows from an actual greedy path. "
                    + "Together with the existing complete_greedy_reward this proves weighted "
                    + "raw optimality for every complete raw greedy path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-terminal-raw-canonical"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Optimality.terminal_raw_canonical"),
                H("Ordered terminality implies canonical raw digits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absence of all five actual adjacent moves forces "
                    + "a gap of at least two between neighboring list entries. Transitivity makes "
                    + "the whole list spaced, hence its raw multiplicities are binary and "
                    + "nonconsecutive. The proof includes the exceptional zero and one splits."))),
                DescribeRole.Theorem),
            Paragraph(Text("OrderedGame/Completion.result combines this raw bound with "
                + "ordered priority correspondence, finite LGS completion and exact potential "
                + "attainment to prove the full source Conjecture17. The universal comparison "
                + "retains all permitted switches and all legal terminal competitors. "
                + "Independent pre-Freeze source-fidelity and declaration-admission review "
                + "passed. Final new-head CI, ordinary merge and independent completion audit "
                + "remain pending. No helper "
                + "counts as a completed external problem. Attribution remains with Bortnovskyi "
                + "et al., Cusenza et al., and the existing suppliers in PRs 7495, 7575, 7643 "
                + "and 7651; no worldwide priority claim is made.")))));
}
