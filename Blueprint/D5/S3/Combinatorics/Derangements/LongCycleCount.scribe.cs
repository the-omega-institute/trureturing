using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Derangements;

internal sealed class LongCycleCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Derangements/LongCycleCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026a378495");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 2 ≤ k ≤ n with 2k > n, the derangements of n labels with a k-cycle number "
            + "C(n,k)(k−1)! D_(n−k).",
        H("Derangements with a unique long cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("long-cycle-count-result"),
                DeclarationHandle.Create(Prefix + "long_cycle"),
                H("The long-cycle count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For 2 ≤ k ≤ n with 2k > n, T(n,k) + C(n,k)(k−1)! D_(n−k) = D_n, so "
                    + "D_n − T(n,k) = C(n,k)(k−1)! D_(n−k) = n! D_(n−k)/(k (n−k)!), with "
                    + "D_0 = 1 and D_1 = 0. A derangement with a k-cycle has cycle type k ::ₘ m′, "
                    + "where m′ is the cycle type of a derangement of n−k labels; since every "
                    + "part of m′ is at most n−k < k, the part k occurs once. The class sizes "
                    + "from Perm.card_of_cycleType_mul_eq then satisfy "
                    + "#(k ::ₘ m′)·k(n−k)! = n!·#m′, and summing over m′ gives the count. This is "
                    + "Lemma 2 of H. Ma and W. Zhang; the identity was proved earlier by L.-H. Su "
                    + "(Proposition 7.4) and later by A. Kallat (Theorem 4.1(c)-(d))."))),
                DescribeRole.Theorem))));
}
