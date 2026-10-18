using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class IidStrictPeakSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent finite ordered samples induce five legal peak modes and exact valley moments.",
        H("Strict Peaks of Independent Ordered Samples"),
        Blocks(Describe.Lean(
            DescribeId.Create("iid-peak-source"),
            DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/IidStrictPeakSource.iid_peak_source"),
            H("The product source and its five-mode pushforward"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be any finite linearly ordered alphabet. Give each letter a nonnegative real mass p(a), with total mass one. The five draws a,b,c,d,e have product mass p(a)p(b)p(c)p(d)p(e). A strict peak at b means a<b and c<b. The three peak events at b,c,d are x,z,y, respectively. Adjacent peaks are impossible, including when letters tie.")),
                Paragraph(Text("The classifier assigns codes 0,1,2,3,4 to null, x only, y only, both x and y, and z. Its pushforward modeLaw is nonnegative and normalized. Write a(b) for the sum of p(a) over a<b. All three occupancies equal the sum of p(b)a(b)^2. With G(c) equal to the sum of p(b)a(b) over b>c, the same occupancy equals the sum of p(c)G(c). The probability of both endpoint peaks is the sum of p(c)G(c)^2.")),
                Paragraph(Text("The determinant modeLaw(0)modeLaw(3)-modeLaw(1)modeLaw(2) equals (1-pi)kappa-pi^2, where pi is the common occupancy and kappa is the joint endpoint mass. The product expectation and the strict comparison classifier define the source independently of these moment identities. Zero letter masses and one-letter alphabets are permitted."))),
            DescribeRole.Theorem))));
}
