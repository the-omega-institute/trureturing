using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class DyadicResetAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coupled allocation from least-fresh ownership.",
        H("Coupled allocation from least-fresh ownership"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicresetallocation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/DyadicResetAllocation.coupled_allocation"),
                H("Coupled allocation from least-fresh ownership"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be the old physical SMALL inventory with exponents below b, and let a be a fresh label of exponent j<b. Let p>=1 and p+1<=r. Suppose 0<g<2^j and old mass plus g equals p*(2^b-1). For every q<=j suppose the same old low inventory has mass r*(2^q-1). For j<q<=b suppose its mass below 2^q is at least p*(2^q-1)-g. The theorem allocates insert(a,S) into p bins of capacity 2^b-1 and one tail of capacity 2^j-g.")),
                    Paragraph(Text("The lower-scale inequalities use ownership of all r physical occurrences below the least fresh denomination, plus r>=p+1. Higher scales use the residue budget of the original positive bins; adding a supplies its weight to the same physical low inventory. Above 2^b all capacities and coins are small enough that total mass gives the condition. The abstract labelled allocator constructs the partition. select_power is its consumed two-bin exact-selection application. allocation_total and old_bins_residues transport the original bins without assuming a new allocation or favorable gate.")),
                    Paragraph(Text("The native all-word consumer derives these hypotheses from Legal and source multiplicities. This helper does not by itself assert their universal availability."))),
                DescribeRole.Theorem)), []));
}
