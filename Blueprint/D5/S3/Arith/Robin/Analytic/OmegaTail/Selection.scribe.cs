using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class SelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual prime capacities and exact second-order cardinality adjustment for finite density selections.",
        H("Selecting prime sets with exact total size"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-capacity"),
                DeclarationHandle.Create(Prefix + "primeInterval_capacity"), H("Capacity of a logarithmic prime window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed 0<a<b, the number of primes in (a*log(x),b*log(x)], divided by y(x)=log(x)/log(log(x)), tends to b-a. The existing prime number theorem is applied separately to both endpoints. Natural floors represent the same actual real-endpoint window."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-count"),
                DeclarationHandle.Create(Prefix + "selectedCount"), H("Exact count above the threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected count K(lambda,x) is floor(T(lambda,x))+1. Its strict relation to the real threshold is retained. The second-order cancellation (K*log(log(x))-log(x))/y tends to lambda; the error is controlled by log(log(x))/y tending to zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adjustment"),
                DeclarationHandle.Create(Prefix + "adjustedSelection"), H("One box absorbs the integer adjustment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every box except one receives floor(r_j*y) primes. The distinguished box receives K minus the sum in the other boxes. This is a natural number by truncated subtraction, and the subsequent theorems prove that the truncation is eventually inactive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-total"),
                DeclarationHandle.Create(Prefix + "adjustedSelection_spec"), H("Exact total and limiting occupancies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite family of nonnegative masses summing to one, with strictly positive mass in the distinguished box, the adjusted occupancies eventually sum exactly to K. Each occupancy divided by y tends to its prescribed mass. The distinguished box has linear slack, whereas rounding and the second-order shift are negligible on that scale."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("capacity-fit"),
                DeclarationHandle.Create(Prefix + "adjustedSelection_fits"), H("Every selected count fits the available primes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If each actual capacity divided by y tends to d_j and r_j<d_j, then eventually all adjusted occupancies fit their capacities simultaneously. Finiteness permits one common cutoff for all boxes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("product-budget"),
                DeclarationHandle.Create(Prefix + "adjustedSelection_budget"), H("Strict logarithmic slack pays the full product budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive upper endpoints b_j and lambda+sum(r_j*log(b_j))<0, eventually sum(k_j*log(b_j*log(x)))<log(x). The exact cancellation K*log(log(x))=log(x)+lambda*y+o(y) is used; the weaker leading relation K/y tending to one would not justify this conclusion."))),
                DescribeRole.Theorem))));
}
