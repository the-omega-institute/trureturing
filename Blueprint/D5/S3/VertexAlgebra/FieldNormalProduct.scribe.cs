using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class FieldNormalProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FieldNormalProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered normal products preserve mode translation covariance.",
        H("Ordered Normal Products"),
        Blocks(
            Paragraph(Text("The product has two pointwise finite coefficient sums. "
                + "Its truncation uses the right field on the input and on finitely "
                + "many actual intermediate states of the left field. Hasse lifting "
                + "and support arguments adapt Carnahan's licensed original source; "
                + "no unproved locality supplier is imported.")),
            Describe.Lean(
                DescribeId.Create("normal-minus-one-translation"),
                DeclarationHandle.Create(Prefix + "normalMinusOne_translation"),
                H("Translation covariance passes through the ordered product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any complex module, any actual endomorphism T "
                    + "and two fields whose nth modes satisfy [T,A_n]=-n A_(n-1), "
                    + "the ordered minus-one product satisfies the same relation. "
                    + "The proof shifts the two finite sums across their zero-mode "
                    + "boundary. It asserts covariance, not locality."))),
                DescribeRole.Theorem))));
}
