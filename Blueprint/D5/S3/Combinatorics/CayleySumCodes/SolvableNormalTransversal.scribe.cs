using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class SolvableNormalTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal transversals and finite solvable groups.",
        H("All normal transversals force a solvable group to be abelian"),
        Blocks(
            Describe.Lean(DescribeId.Create("all-subgroup-restriction"),
                DeclarationHandle.Create(Prefix + "all_restrict"), H("Inheritance by every subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If every subgroup of G has a conjugation-invariant left transversal, "
                    + "the same holds inside any intermediate subgroup M. An actual subgroup "
                    + "L of M is first mapped into G and its given normal transversal is then "
                    + "restricted to M. No subnormality is required. This is NLT inheritance, "
                    + "not inheritance of a perfect or total perfect code."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-subgroup-quotient-inheritance"),
                DeclarationHandle.Create(Prefix + "all_map"), H("All-NLT passes to every quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a surjective group homomorphism, lift each target subgroup to "
                    + "its full preimage. The kernel lies in that preimage, so the specified "
                    + "normal transversal transports to the target subgroup. In particular "
                    + "all-NLT passes to every normal-subgroup quotient. This is an actual "
                    + "subgroup correspondence, not PC or TPC quotient inheritance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("central-transversal"),
                DeclarationHandle.Create(Prefix + "central_transversal"), H("A central transversal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let H be normal and G/H abelian. Every member t of a specified normal "
                    + "left transversal T is central in G: conjugating t leaves its quotient "
                    + "class fixed, and uniqueness of the actual coset representative forces "
                    + "the conjugate to equal t. Finiteness is unnecessary for this step. "
                    + "This is the central-transversal argument used in source Lemma 4.4."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solvable-all-nlt"),
                DeclarationHandle.Create(Prefix + "result"), H("The full finite solvable case"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite solvable group G, if every subgroup is NLT in G, then "
                    + "G is abelian. Strong induction on the actual group cardinal handles the "
                    + "trivial group directly and applies inheritance to the proper derived "
                    + "subgroup in the nontrivial case. Its normal transversal is central; "
                    + "the bijective product of that transversal and the abelian derived "
                    + "subgroup then makes every two elements of G commute. This is Lemma "
                    + "4.4, not the additional arbitrary-finite-group minimal-counterexample "
                    + "and maximal-subgroup partition argument of Theorem 4.5."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/NormalTransversal"))]));
}
