using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qCubicTwiningCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized trace series of the standard cubic lift on P48q",
        H("The P48q Cubic Twining Character"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-trace-term"),
                DeclarationHandle.Create(Prefix + "traceTerm"),
                H("Normalized full-grade trace term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each integer grade n, the actual standard cubic lift acts on the full Sugawara eigenspace. Its trace is multiplied by exp(2 pi i tau (n - 48/24))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-character"),
                DeclarationHandle.Create(Prefix + "actualCubicTwiningCharacter"),
                H("Actual cubic twining character"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The character is the sum of the normalized full-grade trace terms over all integer grades."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-charge-theta"),
                DeclarationHandle.Create(Prefix + "fixedChargeTheta"),
                H("Fixed-charge theta series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theta series sums exp(2 pi i tau E(a)) over the integral charges fixed by the cubic isometry, with E(a) equal to half of the original Gram square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-theta-div-eta"),
                DeclarationHandle.Create(Prefix + "actual_cubic_twining_character_eq_theta_div_eta"),
                H("Absolute convergence and the theta-eta formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For complex tau with positive imaginary part, the actual cubic twining trace terms are absolutely summable. Their sum equals the fixed-charge theta series divided by eta(3 tau) to the sixteenth power.")),
                    Paragraph(Text("The Gaussian bound for the positive P48q Gram controls the fixed-charge terms. The sixteen-colour occupation weights are absolutely summable at exp(2 pi i (3 tau)). The joint family groups by E(a) plus three times the occupation energy. Each fibre is the finite charge cutoff and occupation equation in the full-grade trace formula. Factoring the joint sum and evaluating the unsigned occupation series gives the eta factor, with 3 times 16/24 equal to the vacuum shift 48/24."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-charge"),
                DeclarationHandle.Create(Prefix + "FixedCharge"),
                H("Integral fixed charges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The charges fixed by the standard cubic isometry in the integral P48q lattice."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-dual"),
                DeclarationHandle.Create(Prefix + "fixed_dual_iff_third_fixed_charge"),
                H("Dual of the fixed lattice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A vector in the complex fixed space pairs integrally with every fixed charge exactly when it is one third of an integral fixed charge. The integral norm image certificate identifies the numerators of the projected charges with the fixed lattice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-pairing"),
                DeclarationHandle.Create(Prefix + "fixedChargePairing"),
                H("Fixed-lattice pairing divided by three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The dual identification makes the original Gram pairing of two integral fixed charges divisible by three. The quotient defines the rescaled integral pairing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-pairing-even-pos"),
                DeclarationHandle.Create(Prefix + "fixed_charge_pairing_even_pos"),
                H("Even and positive divided pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The divided pairing has even square on each fixed charge and strictly positive square on each nonzero fixed charge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-fixed-theta-s"),
                DeclarationHandle.Create(Prefix + "fixed_charge_theta_S"),
                H("Inversion of the fixed-charge theta series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On the upper half-plane, the fixed-charge theta series at minus one over tau is its value at tau divided by nine, multiplied by the eighth power of minus i times tau divided by three.")),
                    Paragraph(Text("Sixteen fixed integral rows with an identity column minor identify the fixed charges with integer coordinates. The dual identification proves that the divided coordinate Gram is unimodular, giving square-root determinant three to the eighth power for the original pairing. Reindexing by the divided Gram in the inverse-form theta series gives the argument tau divided by nine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-cubic-twining-character-s"),
                DeclarationHandle.Create(Prefix + "actual_cubic_twining_character_S"),
                H("S transform of the actual cubic twining character"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At minus one over tau, the normalized full-grade trace sum equals the fixed-charge theta series at tau divided by nine over the sixteenth power of eta at tau divided by three. The principal eta transformation at tau divided by three cancels the Poisson inversion factor."))),
                DescribeRole.Theorem))));
}
