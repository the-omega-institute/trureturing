using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GroupActionInvariantStatisticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GroupActionInvariantStatistic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite group actions turn local symmetry into arithmetic conservation.",
        H("Group-Action Invariant Statistics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("swap-invariant-permutation-invariant"),
                DeclarationHandle.Create(Prefix + "swap_invariant_permutation_invariant"),
                H("Transposition invariance extends to every permutation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The preserving permutations form a subgroup. Mathlib's finite generation "
                        + "theorem for transpositions puts every permutation in that subgroup, "
                        + "so a local swap law becomes a global relabeling law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("swap-invariant-is-constant"),
                DeclarationHandle.Create(Prefix + "swap_invariant_is_constant"),
                H("A nonempty finite symmetric statistic is constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The swap exchanging a chosen base point with any target point transports "
                        + "the target value back to the base value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orbit-sum-equals-cardinality-multiple"),
                DeclarationHandle.Create(Prefix + "orbit_sum_eq_card_mul_value"),
                H("Invariant orbit sums are cardinality multiples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A natural statistic constant along a finite group orbit sums to the orbit "
                        + "cardinality multiplied by its value at the base point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orbit-sum-divisibility"),
                DeclarationHandle.Create(Prefix + "orbit_sum_dvd_card"),
                H("Orbit sums satisfy a divisibility law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The orbit cardinality divides every finite natural-valued invariant sum. "
                        + "Failure of this divisibility is a certificate against the proposed "
                        + "group symmetry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("swap-invariant-sum-divisibility"),
                DeclarationHandle.Create(Prefix + "swap_invariant_sum_dvd_card"),
                H("Finite transposition symmetry forces cardinal divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite carrier, the total of a transposition-invariant "
                        + "natural statistic is divisible by the carrier cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fin-sum-divisibility"),
                DeclarationHandle.Create(Prefix + "fin_sum_dvd_card"),
                H("Full symmetry on Fin n forces n-divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive n, a transposition-invariant natural statistic on Fin n has "
                        + "a total divisible by n. This is the concrete arithmetic interface "
                        + "for later residue and counting applications."))),
                DescribeRole.Theorem))));
}
