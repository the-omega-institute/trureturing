using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class MotzkinConvolutionHankelRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed universal first equality chain of Conjecture 7 in arXiv:2502.21050v1 "
            + "is false at r = 4, n = 0. This does not refute a possibly intended restriction r >= 8.",
        H("Motzkin convolution Hankel refutation"),
        Blocks(
            Paragraph(Text(
                "Wang and Zhang, Hankel determinants for convolution powers of Motzkin numbers, "
                    + "arXiv:2502.21050v1, Conjecture 7, prints no lower bound on r. "
                    + "The authors may have intended r >= 8, since Theorems 1–6 cover r = 2 through 7. "
                    + "That interpretation is unverified. This module refutes the printed universal "
                    + "first chain and makes no claim that the authors' intended conjecture is false.")),
            Describe.Lean(
                DescribeId.Create("printed-conjecture-seven-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/MotzkinConvolutionHankelRefutation.result"),
                H("The printed universal first chain is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Motzkin numbers are defined by the source's Catalan-binomial sum. "
                        + "Cauchy convolution defines every natural power, and Matrix.det defines "
                        + "every Hankel size, including the empty determinant. At r = 4, n = 0, "
                        + "the conjectured common value would equate H0 = 1 with H4 = -1. "
                        + "The latter is a private kernel-checked numerical computation. "
                        + "The paper's Theorem 4 is corroboration only and is not a proof premise."))),
                DescribeRole.Theorem)),
        []));
}
