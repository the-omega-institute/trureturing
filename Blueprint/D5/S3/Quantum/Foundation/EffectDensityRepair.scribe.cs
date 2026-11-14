using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectDensityRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace and all-effect lower bounds repair any Hermitian candidate uniformly.",
        H("Uniform density repair"),
        Blocks(
            Paragraph(Text("All matrices are actual complex square matrices indexed by Fin d. IsEffect E means positive semidefiniteness of E and of identity minus E. The error parameter eta is nonnegative and d is at least one in the repair theorem.")),
            Paragraph(Text("The negative spectral projector bounds the trace of the negative part by eta. If the positive part has positive trace, division by that trace produces a positive matrix with complex trace one. If that trace is zero, a coordinate density supplies the required matrix. The same single matrix works for every effect, with correction at most 3*eta.")),
            Describe.Lean(
                DescribeId.Create("negative-projector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector"),
                H("negativeProjector"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Spectral functional calculus of a Hermitian matrix at the indicator of the negative reals defines its negative spectral projector.")),
                    Paragraph(Text("def negativeProjector {d : ℕ} {A : Mat d} (hA : A.IsHermitian) : Mat d := specMap hA (fun x => if x < 0 then 1 else 0)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-projector-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector_effect"),
                H("negativeProjector effect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every Hermitian matrix in every natural dimension, its negative spectral projector and the complement of that projector are positive semidefinite.")),
                    Paragraph(Text("theorem negativeProjector_effect {d : ℕ} {A : Mat d} (hA : A.IsHermitian) : IsEffect (negativeProjector hA)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-negative-projector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.mul_negativeProjector"),
                H("mul negativeProjector"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Multiplying a Hermitian matrix by its negative spectral projector gives the negative of its spectral negative part.")),
                    Paragraph(Text("theorem mul_negativeProjector {d : ℕ} {A : Mat d} (hA : A.IsHermitian) : A * negativeProjector hA = -hermNegPart hA"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psd-effect-pairing-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.psd_effect_pairing_bounds"),
                H("psd effect pairing bounds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an arbitrary positive semidefinite matrix B and every actual effect E, the real part of the complex trace of B*E lies between zero and the real part of the complex trace of B.")),
                    Paragraph(Text("theorem psd_effect_pairing_bounds {d : ℕ} {B E : Mat d} (hB : B.PosSemidef) (hE : IsEffect E) : 0 ≤ (trace (B*E)).re ∧ (trace (B*E)).re ≤ (trace B).re"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psd-trace-real"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.psd_trace_real"),
                H("psd trace real"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complex trace of every positive semidefinite matrix equals the complex embedding of its real part.")),
                    Paragraph(Text("theorem psd_trace_real {d : ℕ} {B : Mat d} (hB : B.PosSemidef) : trace B = ((trace B).re : ℂ)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-density-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.uniform_density_repair"),
                H("uniform density repair"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1, eta>=0 and actual Hermitian A, an error at most eta in its real trace from one and a lower bound -eta for its real trace pairing with every actual effect imply the existence of one actual positive semidefinite rho with complex trace exactly one, uniformly within 3*eta of A on every actual effect. Both positive-trace and zero-positive-trace branches are included.")),
                    Paragraph(Text("theorem uniform_density_repair (d : ℕ) (hd : 1 ≤ d) (η : ℝ) (hη : 0 ≤ η) (A : Mat d) (hA : A.IsHermitian) (htrace : |(trace A).re - 1| ≤ η) (hlower : ∀ E : Mat d, E.PosSemidef → (1-E).PosSemidef → -η ≤ (trace (A*E)).re) : ∃ ρ : Mat d, ρ.PosSemidef ∧ trace ρ = 1 ∧ ∀ E : Mat d, E.PosSemidef → (1-E).PosSemidef → |(trace (ρ*E)).re - (trace (A*E)).re| ≤ 3*η"))),
                DescribeRole.Theorem))));
}
