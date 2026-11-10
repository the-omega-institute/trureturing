using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubgroupGenerating;

internal sealed class GeneratingFibersDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/das2026sgb");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonabelian square-root deficit.", H("GeneratingFibers"), Blocks(
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-generatingpairs"),
                DeclarationHandle.Create(Owner + "generatingPairs"), H("All generating ordered pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a subgroup H of an arbitrary finite group G, generatingPairs H contains exactly every ordered pair (a,b) whose subgroup closure is H, including repeated entries and identities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-paircount"),
                DeclarationHandle.Create(Owner + "pairCount"), H("The actual fiber cardinality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The natural number r_H is the cardinality of generatingPairs H."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-paircount-bot"),
                DeclarationHandle.Create(Owner + "pairCount_bot"), H("The identity fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group, r_bottom=1. Its unique pair is (1,1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-paircount-ge-three"),
                DeclarationHandle.Create(Owner + "pairCount_ge_three"), H("Every other realized fiber has at least three pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If H is not the trivial subgroup and r_H is positive, then r_H is at least three. A nonidentity generator supplies distinct ordered pairs; when both entries are nonidentity and distinct, the six-pair construction applies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-exists-large-fiber"),
                DeclarationHandle.Create(Owner + "exists_large_fiber"), H("A six-pair fiber from noncommutativity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group with a noncommuting pair, some subgroup H has r_H at least six. If a and b do not commute, then a, b and ab are pairwise distinct and a,b are nonidentity. The six distinct pairs (a,b), (b,a), (a,ab), (ab,a), (b,ab), (ab,b) generate the same subgroup. The closure equalities use multiplication and inversion in that subgroup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-sum-paircount"),
                DeclarationHandle.Create(Owner + "sum_pairCount"), H("The complete fiber partition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Summing r_H over all subgroups gives card(G)^2, by partitioning every ordered pair according to its generated subgroup. Subgroups with zero fibers remain in the index type."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-paircount-prime"),
                DeclarationHandle.Create(Owner + "pairCount_prime"), H("Prime-order fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If the actual subgroup H has prime order p, then r_H=p^2-1. Every pair in H other than (1,1) generates H, using the prime-cardinality subgroup dichotomy. The proof constructs an injective correspondence with these pairs; no fiber count is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-exists-prime-fiber"),
                DeclarationHandle.Create(Owner + "exists_prime_fiber"), H("An actual Cauchy subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group of order greater than one, Cauchys theorem supplies a prime p and an actual subgroup H of cardinality p with r_H=p^2-1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-positivefibers"),
                DeclarationHandle.Create(Owner + "positiveFibers"), H("The realized subgroup set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The finite set consists exactly of the subgroups H with positive r_H. This set is used only to count realized fibers, and does not remove isolated subgroup vertices from the graph."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sgb-generatingfibers-sqrt-sum-le-deficit"),
                DeclarationHandle.Create(Owner + "sqrt_sum_le_deficit"), H("The nonabelian square-root deficit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let M=card(G)^2 and t be the number of positive fibers. For every finite nonabelian G, the sum of sqrt(r_H) over all subgroups is at most M-t. The trivial fiber r=1 costs one unit relative to sqrt(r)<=r-1. Every other positive fiber has r>=3 and satisfies that inequality; a six-pair fiber satisfies sqrt(r)<=r-2 and supplies the missing unit. Summing this pointwise bound cancels both corrections. This estimate concerns fibers realized by one actual group."))), DescribeRole.Theorem))));
}
