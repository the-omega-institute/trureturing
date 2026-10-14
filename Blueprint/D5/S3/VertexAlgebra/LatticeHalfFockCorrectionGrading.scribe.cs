using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCorrectionGradingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weight of the native twisted correction",
        H("Shift and original oscillator weight"),
        Blocks(
            Paragraph(Text("The construction uses the original singletonPolynomial, pairPolynomial, pairDerivation, insertion, correctionWord and Corr. The auxiliary coordinate none has weight one and coordinate some(i,n) has the original oscillator weight n+1. Neither the original oscillatorEuler nor any physical field is redefined.")),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-word-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_weighted"),
                H("The actual correction word has its exact original total weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The real singleton coefficient multiplies the auxiliary coordinate to power n+1. The real pair coefficient multiplies it to the sum of the two original weights, with the actual Gram entry and pairScalar unchanged. correctionWord_matching and labelledRemainders_size supply the exact remaining weight for every repeated occurrence. Strong induction on word length includes empty words, arbitrary charge, nonorthonormal Gram and rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-coefficient-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_coefficient_weight"),
                H("Every nonzero shift coefficient retains weight W minus s"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Actual optionEquivLeft coefficient extraction identifies the exponent with optionElim. The additive weight is exactly s plus the remaining oscillator weight. This consequence of correctionWord_weighted is stronger than a shift bound and yields Corr_Euler."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-original-euler"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.Corr_Euler"),
                H("Corr intertwines the original Euler operator with the shift count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every complex finite polynomial p and natural s, oscillatorEuler(Corr(p)[s])+s Corr(p)[s]=Corr(oscillatorEuler(p))[s]. Monomial enumeration has the exact word weight. Polynomial linear extension includes arbitrary finite mixtures; zero and absent coefficients need no homogeneous-input assumption. oscillatorEuler_monomial identifies the original diagonal action on every monomial."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classical twisted lattice correction is described by FLM and the Dong-Nagatomo and Bakalov-Kac sources. Its exact weight identity supports L0 covariance; it does not establish full twisted Jacobi, fusion, a Monster action, string theory or AdS/CFT.")))));
}
