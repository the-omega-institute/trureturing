using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialDiskCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same original period has a normalized holomorphic correction, continuation and nome.",
        H("The normalized native disk primitive"),
        Blocks(
            Describe.Lean(DescribeId.Create("disk-definition"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk"),
                H("The full unit disk"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D is the open ball with center zero and radius one in the complex plane."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("r-definition"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.R"),
                H("The reciprocal Abel coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("R(r)=1/((1-r)P(r) squared), where P is the literal original period. Its denominator is nonzero throughout D."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("g-definition"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.G"),
                H("The removable native difference quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("G=dslope R 0, so its value at zero is the actual derivative of R at zero, and away from zero it is (R(r)-R(0))/r."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("h-definition"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.H"),
                H("The normalized disk correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H is chosen from the disk primitive theorem with H(0)=0 and H prime equal to -iG/pi on D. Its restriction to D is uniquely determined; no regularity outside D is asserted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("disk-correction"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk_correction"),
                H("The normalized native disk primitive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("Let P be the literal original half-binomial-square period on D={r: norm r<1}. The native Picard-Fuchs equation at zero and the literal constant series term give P(0)=1 and P' (0)=1/4. Hence R=1/((1-r)P squared) has R(0)=1 and R' (0)=1/2.")),
                Paragraph(Text("The removable difference quotient G=dslope R 0 is holomorphic on all of D, including zero. It satisfies G(0)=1/2 and rG(r)=R(r)-1. The disk primitive theorem gives H with H(0)=0 and H'=-iG/pi throughout D. In particular H' (0)=-i/(2pi). Any other normalized primitive with this derivative equals H on D, since the difference has zero derivative on the convex disk.")),
                Paragraph(Text("This same H determines the logarithmic continuation t0 and the native nome Q0. Its existence supplies actual functions used in those identities; no new period or arbitrary matching constant is introduced."))), DescribeRole.Theorem))));
}
