using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components;

internal sealed class KetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Kets", H("Components Kets"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2"),
                H("invSqrt2"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("(sqrt 2)^-1 : ℂ, the ubiquitous normalization scalar."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2_mul_self"),
                H("invSqrt2 mul self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Kets.star_invSqrt2"),
                H("star invSqrt2"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma star_invSqrt2 : star invSqrt2 = invSqrt2."))), DescribeRole.Lemma))));
}
