using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMOccupationTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed sources in physical four-point coordinates",
        H("Inverse local coordinates and source transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-occupation-flags"),
                DeclarationHandle.Create(Prefix + "flags"),
                H("Native flags of each physical puncture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first flag is true on the right leg and the second is true for the "
                    + "positive mode sign. In puncture order P, Q, R, S, chart A has flags (false,false), "
                    + "(false,true), (true,false), (true,true). Chart B has (true,false), (false,false), "
                    + "(false,true), (true,true). Chart D has (false,false), (true,false), (false,true), "
                    + "(true,true)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-raw-local"),
                DeclarationHandle.Create(Prefix + "rawLocal"),
                H("Inverse physical displacement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For physical displacement u at a puncture, use the chart scale s "
                    + "and lowering parameter λ to recover the native displacement v = u/(s + λu)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-half-jacobian"),
                DeclarationHandle.Create(Prefix + "halfJacobian"),
                H("Derivative of the lifted coordinate map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the native half-coordinate q, write v = q² and choose "
                    + "the root β of 1−λv that equals 1 at zero. The lifted map is "
                    + "q ↦ scaleRoot(c,x,p)·q/β. Its derivative is scaleRoot(c,x,p)/β³."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-inverse-root"),
                DeclarationHandle.Create(Prefix + "inverseRoot"),
                H("Normalized root in the inverse coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any chart c, real x, puncture p and complex u, write s = scale(c,x,p), "
                    + "λ = loweringParameter(c,p) and v = u/(s + λu). The inverse root is "
                    + "(1 − λv)^(1/2), taken by complex principal power and normalized to 1 at u = 0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-physical-source"),
                DeclarationHandle.Create(Prefix + "physicalSource"),
                H("Signed source in the physical coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any chart c, real x, puncture p and complex u, use the flags (l,e) "
                    + "of p and the inverse coordinate v and root β just defined. The source is "
                    + "legSign(l) · chosenChartSource(c,x,e,v) / (scaleRoot(c,x,p)/β³). "
                    + "The leg sign is −1 on the right and +1 on the left. Put r = parameter(c,x), "
                    + "and let R be 1 for the positive mode and periodRoot(c,x) for the negative mode. "
                    + "The chosen source is t^(−1/2)/(b(v)R) with principal complex power, where t is "
                    + "h(e,v,r)/b(v) in the positive mode and h(e,v,r)/(b(v)(1 − r)) in the negative mode."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-physical-source-analytic"),
                DeclarationHandle.Create(Prefix + "physicalSource_analytic"),
                H("Analyticity in the physical coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < x < 1, the physical source of each chart and puncture "
                    + "is analytic at displacement u = 0. The derivative of the lifted map is nonzero there."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-occupation-signed-physical-source-transport"),
                DeclarationHandle.Create(Prefix + "signed_physical_source_transport"),
                H("Source germs on the B and D overlaps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix real 0 < x < 1 and any puncture p. Write M_c(u) for physicalSource "
                    + "in chart c. On a neighborhood of u = 0, both (−i√x)⁻¹ M_A(u) = relativeB(p) M_B(u) "
                    + "and i⁻¹ M_A(u) = relativeD(p) M_D(u) hold, with √x the positive real root. "
                    + "The B sign is −1 at S and +1 elsewhere. The D sign is −1 at Q and R and +1 elsewhere. "
                    + "The squared sources become the same reciprocal physical polynomial after the lift "
                    + "factors are included. Their signed sums are nonzero at the origin by the center "
                    + "normalization and remain nonzero on a neighborhood, so equality of squares "
                    + "gives equality of the signed sources there."))),
                DescribeRole.Theorem))));
}
