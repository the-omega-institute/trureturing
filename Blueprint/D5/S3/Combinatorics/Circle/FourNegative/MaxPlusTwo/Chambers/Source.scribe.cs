using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical shadow and charge",
        H("Construction and exact scope"),
        Blocks(Paragraph(Text("The internal source_shadow_charge derives q=2f-g and z=g-f from the accepted SourceTable.source_table. For the four physical positive chains U,V,W,X, the shadow bases are A,DC,D(R+1)Z,DTZ and the charge bases are 0,1,Z+1,TZ+T+1. The old f bases equal the shadow base plus the charge base. At the four negative physical labels, z is -B+DC/2,-B+D(R+1)Z/2,-B+DTZ/2,-B and q is 1,Z/2+1,T(Z+1)/2+1,(A+1)/2. The fresh enlarged-source label has value A. This source identification imposes no coprimality or distinct-numeric-value assumption."))), []));
}
