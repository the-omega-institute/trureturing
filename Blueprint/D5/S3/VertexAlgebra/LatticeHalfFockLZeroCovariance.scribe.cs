using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockLZeroCovarianceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full native twisted Sugawara zero-mode covariance",
        H("Actual operators on every source and target state"),
        Blocks(
            Paragraph(Text("The source operator is exactly LatticeSugawaraConformal.sugawaraMode D H 0 on the original complete Carrier D. The target operator is the existing LatticeHalfFock.tensorL D (ActualGround D hu) H 0 on the complete ActualTensor D hu. The field is the original corrected Ytw. Both inverse-Gram equations and hu:IsUnit D.G.det are explicit; no positivity, signature, dimension, occupation or charge restriction is added.")),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-word-native-lzero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockLZeroCovariance.normalWord_L0"),
                H("Native L0 commutes through every unrestricted normal word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The completed charged_tensor_L0_covariance is applied to the genuine chargedCoefficient. The existing current commutator gives current mode q the weight -(q+1/2), including both signs. jetScalar does not change it. Every recursive flatCoefficient shifts the charged exponent by 2q+2n+3, so the sum of weights is W+(E+chargeNorm)/2. normalWord_flattened and actual flatTerm_finite justify mapping and splitting the full tuple sum on arbitrary finite tensor vectors. No aggregate order is used to bound an individual branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-full-original-sugawara-lzero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockLZeroCovariance.Ytw_L0_covariance"),
                H("Full corrected Ytw intertwines original Sugawara L0"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every original source a, integer E and actual tensor v, L0(Ytw(a)[E]v)=Ytw(a)[E](L0v)+Ytw(originalL0(a))[E]v+(E/2)Ytw(a)[E]v. At shift s, actual shiftLinear evaluates the coefficient at E+2s while Corr_Euler lowers the original oscillator weight by s. Their contributions cancel exactly. Finite correction and source sums retain every charge and arbitrary complex coefficient. The original sugawaraMode_weighted_homogeneous and oscillatorEuler_monomial suppliers recover the charged norm divided by two and the original oscillator energy. This is an operator proof, not an assumed twisted-module law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-physical-homogeneous-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockLZeroCovariance.Ytw_homogeneous_coefficient"),
                H("Actual homogeneous coefficient shifts original conformal energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("If a is an original Sugawara eigenstate of complex energy h and v is a native tensorL0 eigenstate of energy t, then its coefficient has energy t+h+E/2. The completed Ytw_omega identifies the target with coefficient -4 of the original conformal state, including the unchanged rank/16 ground offset and quadratic G(i,j)/8 correction. homogeneousCoefficient consumes this consequence to construct a linear map between the genuine operator eigenspaces. No spectral decomposition, finite-dimensional energy fiber or positive spectrum is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The formula includes the original -beta/2 singleton, repeated and empty words, and both signed current branches. This is the classical L0 covariance relation with unrestricted finite-support sums.")),
            Paragraph(Text("Full Virasoro covariance, twisted Jacobi and translation, Monster moonshine, fusion and anomalies, full CFT and string theory, emergence of spacetime and AdS/CFT remain open. L0 covariance does not establish any of them.")))));
}
