using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimFixedBoardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimFixedBoard.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/morisawa2026mpileperiodicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual fixed-board sequence has an eventual period, and its least "
            + "positive eventual period divides every eventual period.",
        H("Fixed-board Divisor Nim sequences"),
        Blocks(
            Paragraph(Text("A position is a finite multiset of positive natural heap sizes. "
                + "A move selects one occurrence h and removes an amount d between one and h "
                + "that divides every untouched occurrence. A zero remainder is deleted. "
                + "The empty position has value zero. The function adjoinHeap omits a varying "
                + "heap at n=0, and fixedSequence is the actual native Grundy value of this position. "
                + "Heap sizes, cardinalities and repeated occurrences are unrestricted.")),
            Node("zero-omission-periods", "The exact bridge for the zero convention",
                "tail_period_iff_fixed_sequence",
                "For every fixed multiset A and natural T, the existing HasTailPeriod A T "
                    + "holds exactly when the omission-aware actual sequence fixedSequence A "
                    + "has eventual period T. Increasing a threshold by one ensures both "
                    + "varying indices are positive. Thus the least eventual period is "
                    + "unchanged by omitting the varying zero heap."),
            Node("fixed-move-data", "Selected fixed moves", "mem_fixedMoveData",
                "For every multiset A and natural h,d, the pair (h,d) belongs to fixedMoveData A "
                    + "exactly when h is an occurrence in A and legal A h d holds. Erasing h "
                    + "removes one occurrence; equal heap sizes do not impose distinctness."),
            Node("literal-recurrence", "Equality of the actual follower sets", "fixed_board_recurrence",
                "Let A be positive and nonempty, and n at least gcd(A). The actual follower-value "
                    + "set of adjoinHeap A n equals the union of fixedSequence A (n-d), over every "
                    + "positive divisor d of gcd(A), and fixedMoveValues A n. The latter set contains "
                    + "fixedSequence (successor A h d) n for every actual fixed move with d dividing n. "
                    + "It includes an empty fixed successor and legal deletion. Both inclusions hold."),
            Describe.Lean(DescribeId.Create("period-existence"),
                DeclarationHandle.Create(Prefix + "fixed_board_eventually_periodic"),
                H("Eventual periods for every nonempty fixed board"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive nonempty multiset A there is a positive "
                    + "natural T and a threshold N such that g((n+T) adjoined to A)=g(n adjoined to A) "
                    + "for all n at least N. Induction on the total fixed stones supplies periods for "
                    + "all nonempty fixed successors. Their periods and every legal removal amount "
                    + "have a common positive multiple. A single threshold works for the finitely "
                    + "many fixed moves.")),
                    Paragraph(Text("The uniform bound confines tail values to zero through twice "
                        + "the fixed sum. Deleting the sole fixed heap leaves a singleton of actual "
                        + "value n, which exceeds this bound on the tail and does not affect the mex. "
                        + "Full gcd-length blocks sampled at the same forcing phase lie in a finite "
                        + "set. Two equal blocks propagate by the exact native recurrence and give "
                        + "a positive period."))),
                DescribeRole.Theorem),
            Node("least-period", "Divisibility of the least period", "fixed_board_least_period",
                "For every positive nonempty A, leastTailPeriod A is positive, is an eventual "
                    + "period, and divides every eventual period T. Differences of ordered tail "
                    + "periods are tail periods. Reducing T modulo the least positive period "
                    + "therefore forces zero remainder. The value at n=0 retains its omission convention."),
            Node("fixed-minimum", "The actual minimum heap", "fixed_minimum_spec",
                "For every nonempty multiset A, fixedMinimum A belongs to A and is at most every "
                    + "member of A. The definition assigns zero to the empty multiset."),
            Node("comparison-signal", "The complete periodic fixed-option signal", "comparison_spacing_signal",
                "Let A be positive and nonempty and H its minimum. The comparisonSpacing A is the "
                    + "least common multiple of lcm(1,...,H) and the leastTailPeriod values of every "
                    + "nonempty actual direct fixed successor. It is positive, is divisible by "
                    + "lcm(1,...,H), and is divisible by each of these actual least periods. "
                    + "The whole set fixedValues A n of nonempty fixed-follower SG values repeats "
                    + "after this spacing for every sufficiently large n. The empty fixed successor "
                    + "is retained separately in the literal recurrence.")), []));

    private static DocumentBlock Node(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
