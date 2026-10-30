using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class DyadicAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact labelled dyadic allocation.",
        H("Exact labelled dyadic allocation"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicallocation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/DyadicAllocation.allocation_iff_residues"),
                H("Exact labelled dyadic allocation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be a finite set of distinct physical labels, e assign an arbitrary natural exponent to every label, and let a finite type index natural bin capacities b. Assume the coin total sum over S of 2^e equals the sum of all capacities. Allocation means a disjoint partition of the original labels among the bins, with every label used exactly once and each bin sum exactly its capacity. The theorem characterizes Allocation by the inequalities sum_i (b_i mod 2^q) <= sum_{a in S, e(a)<q} 2^e(a), for every natural q. No injectivity, complete denomination ladder, nonempty type, positive capacity, or multiplicity restriction is assumed.")),
                    Paragraph(Text("Necessity filters each actual bin below the same scale and sums the disjoint physical pieces. Sufficiency deletes an actual maximal-exponent coin. The inequality at its denomination forces a bin with at least that residual capacity. Subtracting its weight preserves every lower-scale residue. Above the maximal denomination every remaining coin is low, so total mass suffices. Strong induction on the finite physical set terminates at the empty set, including when no bins exist. Numerical ties remain separate labels.")),
                    Paragraph(Text("The exact-power selection used by the native exchange is an application with two capacities, not a second allocation algorithm. The native coupled consumer supplies the residue inequalities from the same old inventory and the least fresh physical denomination. This abstract theorem alone does not establish arbitrary-source Circle C3.1."))),
                DescribeRole.Theorem)), []));
}
