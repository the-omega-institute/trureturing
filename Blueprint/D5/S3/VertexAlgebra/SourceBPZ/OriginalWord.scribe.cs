using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class OriginalWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional labelled original-carrier BPZ induction.",
        H("Original Word BPZ Transpose on the Actual Carrier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-word-choice-charge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.word_choice_charge"),
                H("Finite charge support of every actual word field"),
                StatementSource.FromAuthor(Disp(Call("word_choice_charge", F.Id("D"), F.Id("α"), F.Id("w"), F.Id("n"), F.Id("v")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem uses the actual Carrier and actual recursive wordField. " +
                    "Each integer mode of an actual word field maps one charge sector into " +
                    "the translated sector, with no generic or half-carrier replacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-word-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceBPZ/OriginalWord.actual_word_transpose"),
                H("Conditional labelled word transpose"),
                StatementSource.FromAuthor(Disp(Call("actual_word_transpose", F.Id("D"), F.Id("B"), F.Id("α"), F.Id("w")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every actual oscillator word, the finite transpose sum retains each " +
                        "labelled occurrence and has a deletion branch with the charged zero-mode " +
                        "coefficient and nondeletion branches with binomial coefficients.")),
                    Paragraph(Text(
                        "The result is conditional on the explicit actual current transpose, the " +
                        "actual word zero-mode covariance supplier, and the charged-primary transpose " +
                        "supplier. It consumes the compiled finite scalar insertion theorem and does " +
                        "not assume an all-source BPZ law."))),
                DescribeRole.Theorem))));
}
