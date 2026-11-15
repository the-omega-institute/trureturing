using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT;

internal sealed class MathematicsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Mathematics", H("Primitives QFT Mathematics"), Blocks(
            Paragraph(Text("For every natural n, the source constant QuantumAlg.ω n is exp((2 pi / 2^n) i). Its positive sign fixes the forward-transform convention, and n equal to zero is included.")),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_pow_eq_one"),
                H("omega pow eq one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every natural n, ω_n ^ (2^n) = 1. This states that 2^n is a period."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN"),
                H("invSqrtN"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("QFT normalization factor: 1/√(2^n), generalizing NormalizedVector.invSqrt2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN_succ"),
                H("invSqrtN succ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Recursive normalization of the Fourier transform."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_sq"),
                H("omega succ sq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The root for an n-qubit transform is the square of the root for the next larger transform."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_half"),
                H("omega succ pow half"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The halfway power of the (n+1)-qubit Fourier root is minus one."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_period_mul"),
                H("omega succ pow period mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma omega_succ_pow_period_mul (n multiplier : Nat) : ω (n + 1) ^ (2 ^ (n + 1) * multiplier) = 1."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration7"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.qftOmega_pair_recurrence"),
                H("qftOmega pair recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Algebraic recurrence of the Fourier phase under the leading-bit/tail split."))), DescribeRole.Lemma))));
}
