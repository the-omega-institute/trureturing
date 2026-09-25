using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteKrausReversibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar error-product condition is equivalent to existence of a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly; the constructed inverse also inhabits the canonical QuantumChannel interface. General bundled-CP Kraus representation remains a separate interface; correctness of the computed spectral candidate is proved in SpectralRecoveryCorrectness.",
        H("FiniteKrausReversibility"),
        Blocks(new[]
        {
            "scalar_products_construct_left_inverse",
            "finite_kraus_left_inverse_iff",
            "canonical_recovery_of_scalar_products"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteKrausReversibility." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/nayaksen2007invertible")),
            Blocks(Paragraph(Text("The scalar error-product condition is equivalent to existence of a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly; the constructed inverse also inhabits the canonical QuantumChannel interface. General bundled-CP Kraus representation remains a separate interface; correctness of the computed spectral candidate is proved in SpectralRecoveryCorrectness."))),
            DescribeRole.Theorem)).ToArray())));
}
