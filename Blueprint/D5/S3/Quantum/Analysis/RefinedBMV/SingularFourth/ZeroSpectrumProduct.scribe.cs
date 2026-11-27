using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth;

internal sealed class ZeroSpectrumProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-copy refined BMV lower bound on singular three-value spectra",
        H("The four-copy refined BMV lower bound on singular three-value spectra"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-four-copy-singular-three-spectrum-product"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumProduct.product_bound_scaled_zero_spectrum"),
            H("Product trace comparison"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "Let p be a positive integer and A and B positive semidefinite in any common finite complex dimension. " +
                "Suppose the spectrum of A is contained in {0,r,t}, where 0 < r < t. " +
                "The mean of the traces of all ordered words with p copies of A and four copies of B " +
                "is at least Tr((A^(p/4) B)^4). The spectral multiplicities and B are unrestricted. " +
                "The proof groups cyclic contractions into three positive Gram blocks and checks the five " +
                "Schur polynomials by exact integer arithmetic and an exponential sum positivity argument."))),
            DescribeRole.Theorem))));
}
