using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class SpectralTransposeRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions.",
        H("SpectralTransposeRecovery"),
        Blocks(new[]
        {
            "spectral_support_projection",
            "spectral_inverse_sqrt_adjoint",
            "spectral_support_mul",
            "inverse_sqrt_sandwich",
            "spectral_support_on_kraus",
            "spectral_transpose_candidate"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/SpectralTransposeRecovery." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/barnumknill2002reversal")),
            Blocks(Paragraph(Text("The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions."))),
            DescribeRole.Theorem)).ToArray())));
}
