using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class LabeledZetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/LabeledZeta",
            "A labeled Dirichlet vector remains nonzero at every spectral parameter."),
        H("Labeled Zeta Vectors"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("labeled-zeta-vector-never-vanishes"),
                DescribeKind.Theorem,
                H("The labeled vector never vanishes"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert")),
                Blocks(Paragraph(Text(
                    "The coordinate product needs no summability claim. Its empty-ledger coordinate is one, so the kernel-checked function cannot equal the zero vector."))),
                LatexStatement.Create(@"$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ \operatorname{labeledZeta}(\ell,s)\neq 0$")))));
}
