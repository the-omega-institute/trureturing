using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class DyadicResetDenominationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical multiplicities and low-denomination budgets.",
        H("Physical multiplicities and low-denomination budgets"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicresetdenominations"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/DyadicResetDenominations.low_mass"),
                H("Physical multiplicities and low-denomination budgets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive m and natural r and q<=m, the sum of 2^(i mod m) over all physical labels i in Fin(m*r) with i mod m<q equals r*(2^q-1). The sum includes all r distinct occurrences of each denomination. The proof fibers by the physical residue, uses residue_card from the source owner, and evaluates the geometric sum. Missing bins, zero r and q=0 are not excluded.")),
                    Paragraph(Text("For native m>=3,r>=1, positive, top and reset labels are classified by their original residue. The two LARGE classes each have r occurrences, so total LARGE weight is 2*r. large_used_counts counts exactly the consumed top and reset occurrences of any list. These identities feed both the arbitrary-word augmentation and the universal competitor obstruction."))),
                DescribeRole.Theorem)), []));
}
