using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaFixedDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed source action on the odd target kernel",
        H("Fixed source action on the odd target kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-sigmatensor-involutive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.sigmaTensor_involutive"),
                H("Target reflection squared is identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Tensor induction applies the existing original oscillator involution to every actual tensor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-oddtarget"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.oddTarget"),
                H("The literal odd kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("This submodule is ker of sigmaTensor plus the identity. No claim identifies it with an independently proved integral spectral sector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-ytw-fixed-oddtarget"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.Ytw_fixed_oddTarget"),
                H("Fixed source coefficient closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Target conjugation proves closure for every theta-fixed source and every cover coefficient, with no source or target homogeneity premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-restrictedcoefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.restrictedCoefficient"),
                H("Actual restricted coefficient maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The values are the original Ytw coefficient actions, with only a kernel-membership proof added."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-restrictedcoverfield"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.restrictedCoverField"),
                H("The actually truncated restricted field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original source lower-truncation supplier constructs the actual HVertexOperator on the odd kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-restrictedcover-even-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.restrictedCover_even_coefficients"),
                H("Odd cover coefficients vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original source monodromy selection and fixed source equation prove the zero odd-cover coefficients. This parity consequence is reused mathematics, not independent numeric endpoint credit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-restrictedcover-vacuum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.restrictedCover_vacuum"),
                H("Original vacuum restriction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original Ytw_vacuum supplier yields the identity field on the odd target kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-originalfixednativeaction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.originalFixedNativeAction"),
                H("The proved original fixed native action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The constructed action contains the actual truncated restricted fields, their literal original coefficient actions, odd-cover zero identities and the original vacuum identity. Each law is proved for this original field rather than assumed. This is not a twisted module or Jacobi structure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetafixed-physicalhomogeneouscoefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.physicalHomogeneousCoefficient"),
                H("The correctly indexed original weight map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The physical coefficient is literally coeff of minus twice the integer mode minus two. Both inverse-Gram equations and the source and target eigenspace conditions give target weight k plus r minus n minus one. No spectral classification or twisted Jacobi law is assumed."))),
                DescribeRole.Definition))));
}
