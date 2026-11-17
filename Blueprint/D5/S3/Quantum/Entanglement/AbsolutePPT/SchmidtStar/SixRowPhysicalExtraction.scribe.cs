using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowPhysicalExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual six-row APPT supplies every physical scalar constraint on one original spectrum", H("SixRowPhysicalExtraction"), Blocks(
            Describe.Lean(DescribeId.Create("sixrowphysicalextraction-literal-physical"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction.literal_physical"),
                H("literal APPT physical extraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least 23, start with an ordered, nonnegative, unit-mass spectrum l and APPT of its diagonal in the supplied product labelling. Set U=l[6n-21], B=l[14], r=(B-U)/U, h_i=(l[i]-B)/U for the first fifteen slots, and d_j=(U-l[6n-21+j])/U for the last twenty-one. Literal moments give U>0 and the two actual zero slots h_14=d_0=0. The coupling of the same l and labelling gives the squared coupled inequality. The slack and head cap agree with their scalar definitions. This yields PhysicalScalarHyp r H D a q on the sums and squared sums of those same lists, including a>=0 and the zero-slot Cauchy bounds H^2/14<=a and D^2/20<=q."))), DescribeRole.Theorem)
        )));
}
