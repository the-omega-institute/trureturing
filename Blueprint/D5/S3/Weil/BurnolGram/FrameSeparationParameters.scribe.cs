using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.BurnolGram;

internal sealed class FrameSeparationParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/BurnolGram/FrameSeparationParameters.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite frame geometry supplies the radius and positive squared gaps needed by the sparse negative Weil certificate.",
        H("Frame Separation Parameters"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frame-separation-exists-parameters"),
                DeclarationHandle.Create(Prefix + "exists_frame_separation_parameters"),
                H("Every frame admits separation parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of node norms bounds every node. Injectivity of nodeEquiv and the stored signSeparated field exclude equal squares for distinct labels in all four plus/minus combinations. The exception set removes every selected four-point orbit, so injectivity of gamma and its reflection and conjugation identities exclude target-to-exception square collisions. Finite positive minima choose the nodal gap first and the exception gap afterward; empty sets use one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frame-separation-arithmetic-negative-certificate"),
                DeclarationHandle.Create(Prefix + "exists_arithmetic_sparse_negative_certificate"),
                H("The full certificate with only arithmetic premises"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the radius and both gaps before the arithmetic inputs. The existing finite-data theorem then gives positive definiteness of the negative full Gram matrix, exact negative index, the original support bound and the original quadratic margin at every depth above the rational threshold. The cutoff comparison, budget comparison and integer conditions remain premises. The theorem assumes a frame and does not assert a nonempty off-line frame exists."))),
                DescribeRole.Theorem)), []));
}
