using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaCoefficientsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original charged target reflection",
        H("Original charged target reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-sigmatensor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.sigmaTensor"),
                H("Target oscillator reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The target map is literally TensorProduct.map of the original oscillator sigmaLinear and the identity on the actual chosen ground representation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-sigma-halfcreationcoeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.sigma_halfCreationCoeff"),
                H("Every signed half-creation index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual power-series substitution and coefficient map prove charge reflection. Negative integer coefficient indices retain the original zero branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-sigma-halftranslatedpolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.sigma_halfTranslatedPolynomial"),
                H("Literal translated polynomial covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original translation variables, Gram pairing and odd powers are unchanged. Polynomial coefficient mapping gives the translated target sigma, without a substitute translation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-sigma-oscillatorcoefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.sigma_oscillatorCoefficient"),
                H("The genuine finite oscillator sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual oscillatorTerm support lies in the translated polynomial support. The checked additive map transports that finite finsum, for every target polynomial and exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-ground-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.ground_reflection"),
                H("Chosen quotient ground reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("This is an explicit checked consumer of the unchanged private ground_neg proof. It identifies the reflected section in the quotient K, not the representation of the group inverse and not a parity-phase substitution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetacoefficients-sigmatensor-chargedcoefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients.sigmaTensor_chargedCoefficient"),
                H("Arbitrary target charged intertwining"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The complete tensor carrier is covered by tensor induction. The existing chargeScalar and chargeNorm are preserved and the chosen representation is never replaced."))),
                DescribeRole.Theorem))));
}
