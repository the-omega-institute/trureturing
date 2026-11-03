using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class FiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak: structural parameter split", H("Finite"),
        Blocks(Paragraph(Text("The finite parameter split p in {4,8,16,32}, q in {2,4,8,16,32}, h in {1,2} consumes the unbounded q-two, q-four, q-eight, q-sixteen and q-thirtytwo structural selectors. Every branch uses the same original Good predicate: strict physical stocks, literal dyadic submask, and all original old/new windows. The positive BoundaryRow table and all its certification declarations are absent. The surrounding Large and Small arguments and the original A2 endpoint retain their statements. This split is a consumed application of structural results, and adds no independent mathematical content.")),
            Describe.Lean(DescribeId.Create("finite-exists"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.finite_exists"), H("finite_exists"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For natural p,q,h, if p=4 or p=8 or p=16 or p=32, q=2 or q=4 or q=8 or q=16 or q=32, and h=1 or h=2, there exist natural v,m,M and before:Bool such that Good p q h v m M before."))), DescribeRole.Theorem)), []));
}
