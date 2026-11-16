using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class C3GatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal doubled gates for c=3,a=5", H("Universal doubled gates for c=3,a=5"),
        Blocks(
            Describe.Lean(DescribeId.Create("c3-doubled-gates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3Gates.c3_doubled_gates"),
                H("c3_doubled_gates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The public domain e>=2 uses the exact c3Banks, beta=12 and the original alpha allocation. The e=2 chart retains its W2q contribution; e=2 through 7 and both parity tails are included. The terminal order is [0,3,2,1], with the last new successor OLD A. Polynomial identities and shifted positive coefficients prove the gates for all natural ell, rather than sampled controls. Attribution: uxwv-c3-a5-full-tail-20261102.py."))),
                DescribeRole.Theorem)), []));
}
