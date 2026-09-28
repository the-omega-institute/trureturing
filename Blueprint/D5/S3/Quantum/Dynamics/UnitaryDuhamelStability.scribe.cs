using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class UnitaryDuhamelStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive noncommutative Duhamel interpolation for the genuine exponential unitaries. Bounds use the C-star operator norm; trace-distance and free-energy extensions remain separate.", H("Actual Unitary Duhamel Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("evolution-coe"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolution_coe"),
                H("evolution coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The evolution is built using Mathlib selfAdjoint.expUnitary and the genuine Banach-algebra exponential."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("evolution-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolution_zero"),
                H("evolution zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("evolution-hasderivat"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolution_hasDerivAt"),
                H("evolution hasDerivAt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("evolution-hasderivat-prime"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolution_hasDerivAt'"),
                H("evolution hasDerivAt'"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bridge-hasderivat"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.bridge_hasDerivAt"),
                H("bridge hasDerivAt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiate the actual two-generator interpolation. The Hamiltonians need not commute, and no derivative or Duhamel formula is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bridgederivative-norm"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.bridgeDerivative_norm"),
                H("bridgeDerivative norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unitary factors and the unit-modulus complex scalar give the exact derivative norm, independent of the individual Hamiltonian norms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("duhamel-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.duhamel_identity"),
                H("duhamel identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the fundamental theorem of calculus to the constructed interpolation and its proved derivative."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("evolution-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolution_stability"),
                H("evolution stability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mean-value bound on the interpolation yields the sharp absolute-time operator-norm estimate for all real times."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-conjugation-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.unitary_conjugation_stability"),
                H("unitary conjugation stability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A two-term noncommutative telescoping identity bounds the actual conjugation difference."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("evolved-observable-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/UnitaryDuhamelStability.evolved_observable_stability"),
                H("evolved observable stability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combine the genuine exponential stability theorem with the conjugation estimate. This is not a trace-norm state-distance or free-energy theorem."))), DescribeRole.Theorem))));
}
