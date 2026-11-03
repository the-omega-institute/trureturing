using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact high-d parameters and charged endpoints", H("Exact high-d parameters and charged endpoints"),
        Blocks(
            Paragraph(Text("The ring-valued definitions set z=xq, t=xpq, y=2ht; A=1+x+xy+xyz, B=1+t+xt+xyt, L=1+z+zt+xzt, K=1+y+yz+yzt. The enlarged heads are SU=2B-1, SV=2L-1-z and SW=2K-1-y-yz. These are the original heads used by the small-p selector and its downstream physical consumer.")),
            Paragraph(Text("The first old doubled endpoint is 2vA-2K+2mL, the second is 2B-2K+2ML, and the third is 2B-2L. Their enlarged counterparts are 4vA-2SW+2mSV minus 2A exactly when before is false; 2SU-2SW+2MSV; and 2SU-2SV. The fourth endpoint is zero. The fresh subtraction is part of the endpoint definition, not a relaxed bound."))), []));
}
