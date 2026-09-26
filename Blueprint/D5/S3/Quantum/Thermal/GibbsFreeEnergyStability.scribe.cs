using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class GibbsFreeEnergyStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive pressure and free-energy perturbation bounds using actual Gibbs matrices and a proved spectral Klein inequality.",
        H("Noncommuting Gibbs Free-Energy Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-log"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.raw_log"),
                H("Functional calculus respects the concrete matrix identification"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The C-star to raw matrix map preserves CFC logarithms. Finite spectra justify the restriction even when the first density matrix has a zero eigenvalue."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-relative-entropy-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.gibbs_relative_entropy_nonneg"),
                H("Nonnegativity for the existing Gibbs state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes the newly proved matrix Klein inequality and the existing proof of positive definiteness of the Gibbs density. No relative-entropy nonnegativity hypothesis is supplied."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("expectation-abs-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.expectation_abs_le"),
                H("Dimension-free operator-norm expectation bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive trace-one matrix defines convex weights on an arbitrary Hermitian observable spectrum. The C-star matrix equivalence preserves the Euclidean operator norm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-objective-le-pressure"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.gibbs_objective_le_pressure"),
                H("Gibbs variational inequality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines actual Klein nonnegativity with the existing repository Gibbs variational identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-objective-attained"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.gibbs_objective_attained"),
                H("The constructed Gibbs state attains the pressure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The optimizer is the normalized matrix exponential already present in the repository."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pressure-lipschitz"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.pressure_lipschitz"),
                H("Noncommuting log-partition Lipschitz bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating the two variational objectives at each other's actual Gibbs states gives absolute pressure difference at most the operator norm of the generator difference."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-energy-lipschitz"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.freeEnergy_lipschitz"),
                H("Equilibrium free energy for positive inverse temperature"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exp(H) pressure convention is transformed to exp(-beta H) explicitly. The resulting free-energy constant is one for every positive beta."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("excess-free-energy-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.excessFreeEnergy_identity"),
                H("Physical excess energy-entropy identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuses the Gibbs identity and positive beta; the density can be singular because its thermal reference is faithful."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("excess-free-energy-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.excessFreeEnergy_stability"),
                H("Uniform nonequilibrium free-energy perturbation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An expectation bound and the equilibrium pressure bound yield the factor-two estimate for every joint density matrix. No quantum Pinsker or trace-norm recovery claim is made here."))), DescribeRole.Theorem))));
}
