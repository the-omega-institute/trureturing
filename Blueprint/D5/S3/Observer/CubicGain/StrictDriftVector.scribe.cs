using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class StrictDriftVectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source is P(r,b)=[[r,b],[r(1-r)/b,1-r]], with b>0 and 0≤r≤1",
        H("StrictDriftVector"),
        Blocks(
        Paragraph(Text("The source is P(r,b)=[[r,b],[r(1-r)/b,1-r]], with b>0 and 0≤r≤1. Put j=b+r(1-r)/b, n=j+r, T=1+b and U=1+2b. The actual fourth and fifth M drift coefficients are UΛ and A₅, where Λ=1+6/T+1/U-4/j-4/n and A₅=1+(U+n)(4-15/j+20/T-10/n). They never vanish together, including the endpoints in r.")),
        Paragraph(Text("Clearing positive denominators yields the polynomial numerators N₄ and N₅. An explicit polynomial Bézout identity expresses their combination as 4b⁶(1+b)(1+2b)P_M(b); expanding both sides gives this identity. For 0<b<4 the leading three terms of P_M combine to b¹⁴(27b²+198b-24294)<0 and every remaining term is negative. For b≥4, Λ>0 follows from j,n≥b and b²-b-8>0. These two ranges exhaust the source and exclude simultaneous zeros of Λ and A₅.")),
        Paragraph(Text("The nonvanishing pair (Λ,A₅) allows recovery of the drift offset even when Λ=0. Since U>0, the equivalent pair (UΛ,A₅) also has no common zero.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-fourth-numerator-lambda"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/StrictDriftVector.n4_parentLambda"),
            H("Fourth numerator and drift coefficient"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("When b,j,n,T,U are nonzero, the fourth polynomial numerator N₄ is TU(b²+r−r²)(b²+r−r²+br)Lambda. This identifies the same fourth coefficient in either fifth history."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-lambda-positive-large-b"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/StrictDriftVector.parentLambda_pos_of_four_le"),
            H("Positive fourth coefficient for large b"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every 0≤r≤1 and b≥4, Lambda is strictly positive. The estimates j,n≥b bound the two negative reciprocal terms, while (b²−b−8)/(b(1+b))>0."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-drift-vector-nonzero"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/StrictDriftVector.drift_vector_nonzero"),
            H("drift vector nonzero"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every 0≤r≤1 and b>0, Λ≠0 or A₅≠0. Since U>0, the actual drift coefficients UΛ and A₅ cannot vanish together."))),
            DescribeRole.Theorem))));
}
