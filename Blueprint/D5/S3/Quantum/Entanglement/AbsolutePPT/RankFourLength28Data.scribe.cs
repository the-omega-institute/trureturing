using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class RankFourLength28DataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One proof-carrying rational certificate for the length-28 spectral relaxation.",
        H("Rational length-28 certificate"),Blocks(
            Describe.Lean(DescribeId.Create("rank-four-length28-certificate-data"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Data.certificate"),
                H("Rational matrices with positivity obligations"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("certificate"),Colon,F.Id("Certificate")))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(
                    "The certificate contains P of size 27, an entrywise nonnegative H of size 28, two families B of 28 matrices of size 3, a 2 by 2 family D of matrices of size 3, three C matrices of size 2, and nonnegative vectors w and gamma of lengths 28 and 2. P, the 52 interior B matrices, four D matrices and three C matrices have exact rational LDL factors with 201 strictly positive pivots altogether. Four endpoint B matrices are alpha times v v^T for v=(1,1,0) and nonnegative alpha. Each PositiveRationalMatrix contains its rational matrix and a real PSD proof obtained from QutritSpectralReduction.psd_of_rat_ldl or the rank-one PSD theorem. The endpoint matrices are constructed directly from their weights, without a duplicate array. Signs of H,w,gamma are independent proof fields. H has no PSD field. The data are consumed by RankFourLength28Purity through the full rational-coefficient polynomial identity; positivity of the individual matrices alone does not assert that identity. No solver status is a premise."))),
                DescribeRole.Definition))));
}
