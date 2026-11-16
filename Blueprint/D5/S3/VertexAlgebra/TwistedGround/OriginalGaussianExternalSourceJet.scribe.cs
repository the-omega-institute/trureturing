using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalSourceJetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal Source Derivative and the Actual Jet",
        H("Diagonal Source Derivative and the Actual Jet"),
        Blocks(
            Paragraph(Text("The actual source_pairings_explicit and scaled radial column derivative first differentiate sourceExternal. Multiplication by the original period then differentiates A. This fixes the diagonal jet and feeds the actual displacement and radial equations; it does not assume kernel identification.")),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-sourceexternal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal"),
                H("hasDerivAt_radial_sourceExternal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and 0<r<1, sourceExternal at sqrt(r) has real derivative -(U+V)/(2r F)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-sourceamplitude"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude"),
                H("hasDerivAt_radial_sourceAmplitude"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and 0<r<1, the real derivative of A(r) is Fprime*A/F+(U+V)/(2r); Fprime is shiftedCentralDerivative at shift zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcejetmoment-eq-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative"),
                H("sourceJetMoment_eq_derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and 0<r<1, V equals 2r times the total real derivative of A minus the mode frequency U minus 2r A Fprime/F."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-source-equations"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet.external_source_equations"),
                H("external_source_equations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every pair of signed natural modes and 0<r<1, all three genuine equations hold together: the J frequency sum, the T frequency difference, and the real T radial derivative. Their right sides use U=modeFrequency A and V=2r A derivative-U-2r A Fprime/F, with coefficients (1-r)/2 and the radial divisor 2r retained."))), DescribeRole.Theorem))));
}
