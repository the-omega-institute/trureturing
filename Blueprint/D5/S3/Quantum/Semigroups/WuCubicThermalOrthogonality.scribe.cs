using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicThermalOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gibbs square-root trace pairing is diagonal on the sixteen physical Wu thermal directions.",
        H("Thermal charge pairing and direction weights"),
        Blocks(
            Describe.Lean(DescribeId.Create("pairing-trace-g"),
                DeclarationHandle.Create(Owner + "gibbsPairing_eq_trace_G"),
                H("Gibbs square-root pairing in the G normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("The source pairing is Tr(S Xᴴ S Y), with S = CFC.sqrt(D r), so it is conjugate-linear in X and linear in Y. For r ≥ 1, the positive diagonal matrix G satisfies G⁶ = D, and the theorem identifies S with G³. The same pairing is therefore the trace of G³ Xᴴ G³ Y, which is the normalization used by the downstream translation-energy calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("direction-weights"),
                DeclarationHandle.Create(Owner + "gibbsPairing_direction"),
                H("Exact orthogonality and charge-resolved weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("For a local label in the order identity, lowering E₀₁, raising E₁₀, centered population, the one-mode Gibbs occupations are a = 1/(1 + r³) and b = r³a. The local squared pairing weights are [1, √(ab), √(ab), ab]. A two-mode direction indexed by k = (p,q) is the parity-twisted product of the two local vectors, and its squared weight is the product of the two local weights.")),
                    Paragraph(Text("The local signed charges are 0, −1, 1, 0. The parity phase in the second tensor factor is real and squares to one, so for every r ≥ 0 the pairing of two physical directions vanishes when their two labels differ and equals the product weight directionNormSq r k when the labels agree. The statement includes the endpoint r = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-expansion"),
                DeclarationHandle.Create(Owner + "gibbsPairing_expansion"),
                H("Diagonal coordinate expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("For every r ≥ 0 and arbitrary complex matrices X and Y, expand each matrix in the sixteen directions with the explicit coefficient function from WuCubicThermalBasis. Sesquilinearity in the two arguments and the direction orthogonality give the exact sum of conjugate X-coordinates times Y-coordinates, each multiplied by its two-mode Gibbs weight directionNormSq r k."))),
                DescribeRole.Theorem))));
}
