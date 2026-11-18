using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalJetSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Diagonal Jet Generators", H("Signed Diagonal Jet Generators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcejetmoment-generators"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators"),
                H("sourceJetMoment_generators"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<r<1 and norm(u)+r<1, set x=r and lambdaRatio=the original shifted central derivative at shift zero divided by the period. The positive Vjet sum equals 2x partial_x Mplus minus its explicit U amplitude plus Aminus(0)/2 minus 2x lambdaRatio Mplus. The negative sum multiplied by u equals 2xu partial_x Mminus minus its scaled U amplitude minus Aminus(0)/2 minus 2xu lambdaRatio Mminus. The derivatives are of the actual amplitude series on the diagonal."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcejetmoment-generators-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit"),
                H("sourceJetMoment_generators_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under those same conditions the positive Vjet amplitude is Mplus times [-xu/(1-(1-x)u) -(1-2u+(1-x)u squared)/(2(1-(1-x)u)) -2x lambdaRatio] plus Aminus(0)/2. The negative Vjet sum multiplied by u is Mminus times [xu/(1-x-u) -(u(1-u)/(2(1-x-u))-1/2) -2xu lambdaRatio] minus Aminus(0)/2. Its diagonal derivative has the positive xi-minus sign. These are source-jet identifications, not the terminal J/T kernel identification."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("amplitude-derivative-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.amplitude_derivative_mode"),
                H("amplitude_derivative_mode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign on norm(u)+norm(x)<1, differentiating every actual sourceAmplitude in x and summing against u powers gives the x derivative of sourceMode. Both sourceMode in x and every individual sourceAmplitude are complex differentiable there."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("diagonal-derivative-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.diagonal_derivative_explicit"),
                H("diagonal_derivative_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign on that joint disk, with b=u in the positive case and b=-1 in the negative case, the x derivative of the actual sourceMode equals -b sourceMode/[2(1-u+bx)]."))), DescribeRole.Theorem))));
}
