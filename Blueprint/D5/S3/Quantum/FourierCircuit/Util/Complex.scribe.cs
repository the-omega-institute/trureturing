using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Util;

internal sealed class ComplexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Util Complex", H("Util Complex"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Util/Complex.conj_exp_I"),
                H("conj exp I"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma conj_exp_I (φ : ℝ) : starRingEnd ℂ (Complex.exp (φ * Complex.I)) = Complex.exp (-(φ * Complex.I))."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Util/Complex.exp_I_mul_exp_neg_I"),
                H("exp I mul exp neg I"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma exp_I_mul_exp_neg_I (φ : ℝ) : Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Util/Complex.exp_neg_I_mul_exp_I"),
                H("exp neg I mul exp I"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma exp_neg_I_mul_exp_I (φ : ℝ) : Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1."))), DescribeRole.Lemma))));
}
