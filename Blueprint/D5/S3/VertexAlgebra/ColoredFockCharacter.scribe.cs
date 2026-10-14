using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class ColoredFockCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/ColoredFockCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite-color oscillator energy fiber is counted by an independent partition generating coefficient.",
        H("Colored Oscillator Partition Character"),
        Blocks(
            Paragraph(Text("For a finite color type C, an occupation is a finitely supported function on C times the natural frequencies. Its energy is the sum of (frequency plus one) times occupancy. colorSplit is actual Finsupp currying followed by the finite-domain function equivalence. energy_colorSplit proves exact additivity of the total energy over colors, with the finite outer sum and each finitely supported inner sum justified by the existing sum-curry and sum-fintype laws.")),
            Describe.Lean(DescribeId.Create("all-energy-partition-convolution"),
                DeclarationHandle.Create(Prefix + "energyFiber_card"),
                H("Exact Finite Partition Convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N and finite color type C, the cardinal of the actual energy-N occupation fiber equals coefficient N of (Nat.Partition.genFun with constant weight one) raised to card C. fiberPartitionTuple is an equivalence with the sigma family of energy compositions and tuples of partitions, with both inverse laws. Its dependent right inverse uses Function.hfunext and equality transport between energy fibers with equal underlying occupations; it does not eliminate an equality of dependent function types. Each color uses the existing PolynomialFockCharacter.energyFiberEquivPartition, not a new monochromatic partition proof. EnergyComposition is the finite univ.finsuppAntidiag N; its support and sum conditions are exact. Nat.card_sigma and Nat.card_pi count its partition tuples, and PowerSeries.coeff_prod identifies precisely the same finite convolution. The partition generating function is independent of the oscillator index cardinal."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-color-formal-character"),
                DeclarationHandle.Create(Prefix + "character"),
                H("All Finite Color Counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural c, the formal series whose N-th coefficient counts the full untruncated occupation fiber on Fin c equals genFun(one) to the c-th power. This includes c equal to zero and all N. No state cutoff or numerical level enumeration occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("colored-euler-character"),
                DeclarationHandle.Create(Prefix + "character_euler"),
                H("Euler Product With Finite Color Power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After mapping the natural coefficients to complex numbers, the character equals the c-th power of the formal Euler product over positive frequencies. This uses the existing actual monocolor lZero_character_euler_product and its actual lZero_spectrum. The finite color power remains outside the already justified infinite product: no new infinite-product interchange, analytic convergence assumption or factor truncation is asserted."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are classical oscillator and colored partition counting results, not an originality claim. They do not construct a Monster Lie bracket, a root denominator identity, orbifold fusion, symmetry anomalies, spacetime geometry, full string theory or AdS/CFT. Source-admission enrollment and remote delivery are separate from Lean proof verification.")))));
}
