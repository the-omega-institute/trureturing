using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRaySourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive normalization and identical-row literal histories", H("Positive normalization and identical-row literal histories"), Blocks(
            Paragraph(Text("chartWorld takes any positive chart coordinates x,r, any nonzero whole coefficient vector beta, and any real drift delta to a World d. source_chart_exact supplies the reverse source representation for every original world.")),
            Paragraph(Text("UnnormalizedWorld has a strictly positive rank-one real source R, a nonzero whole coefficient vector for G of degree at most d, and an arbitrary drift. normalizeWorld divides R by its positive trace and multiplies every gain coefficient by that same trace. The resulting source is trace one and the gain remains nonzero.")),
            Paragraph(Text("identicalRow(theta)=[1-theta,theta;1-theta,theta] is legal for 0<theta<1. rowWorld combines this source with any nonzero ordinary coefficient vector and any drift. Its positive source chart is x=1, r=theta/(1-theta). Left multiplication by J fixes the matrix, hence every pure-J cumulative matrix fixes it as well.")),
            Describe.Lean(DescribeId.Create("gain-ray-full-chart-pure-j"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySources.source_chart_pureJ"),
                H("Pure J factors on every legal source chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every positive real x,r and natural n, trace(acquisition(J repeated n) sourceChart(x,r)) equals one when n mod 2 is zero, and equals (x+r)/(1+xr) otherwise. Both factors are strictly positive on the positive chart. The equality uses the literal native power interface and J squared equal to the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysources-normalized-readAt"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySources.normalized_readAt"),
                H("Every unnormalized original-clock read is preserved"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d, UnnormalizedWorld W, chronological word w and natural clock i, readAt(normalizeWorld W,w,i) equals gain(d,W.coeff)(i) trace(acquisition(take i w) W.source)+W.drift. The same single source and whole polynomial are used at every clock."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysources-identical-row-legal"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySources.identical_row_legal"),
                H("Every identical-row source in the open interval is legal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real theta with 0<theta<1, identicalRow theta is strictly entrywise positive, has matrix rank one, and has trace one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysources-identical-row-readings"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySources.identical_row_readings"),
                H("All pure-J reads use the original whole gain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d, theta with 0<theta<1, nonzero beta:Coeff d, real drift delta and natural n, readings(rowWorld(d,theta,beta,delta),J repeated n) is the vector gain(d,beta)(i)+delta at its original Fin(length(J repeated n)+1) clocks. This includes the initial read and the empty action word. No sampled-zero, sign or lower-degree case is excluded."))), DescribeRole.Theorem))));
}
