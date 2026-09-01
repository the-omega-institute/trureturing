using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class LedgerDeficitSecondVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared norm-deficit second variation, its mirror-antisymmetric zero address, and the Dirac measure embedding.",
        H("Ledger Deficit as a Second Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-deficit-curve"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.normDeficitCurve"),
                H("Squared norm-deficit curve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a signed ledger displacement d, the auxiliary curve is (exp(-d u) - 1)^2. " +
                    "It measures squared distance from the unitary norm at u = 0, so the first-order " +
                    "orientation is discarded and the local quantity is a nonnegative energy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ledger-deficit-second-variation"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation"),
                H("Chosen second variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected candidate is ((N - 1)^2)''(0) for N(u) = exp(-u), evaluated along " +
                    "the ledger displacement rate. This is the squared-distance Hessian of the norm " +
                    "coordinate to the unitary value 1. The logarithmic candidate is flat in this coordinate; " +
                    "the unsquared norm candidates retain a signed first variation and therefore do not give " +
                    "the centered loss geometry. The definition satisfies the machine identity " +
                    "ledgerDeficitSecondVariation d = 2 d^2 and is consequently nonnegative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ledger-deficit-second-variation-identity"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_eq"),
                H("The defining Hessian identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiating the exponential curve twice and applying the product rule gives exactly " +
                    "twice the square of the signed displacement. This is a definition-level algebraic check, " +
                    "not a claim about the zeta zero set or about the open Weil bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-ledger-address"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.zeroLedgerAddress"),
                H("Canonical zero-to-ledger address"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A zero rho is assigned the mirror-antisymmetric address rho - mirror(rho). " +
                    "The address is canonical from the already frozen reflection geometry: it vanishes on " +
                    "the critical fixed locus and changes sign under the mirror. No enumeration order or " +
                    "external labeling is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-part-ledger-length"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.realPartLedgerLength"),
                H("Length on complex addresses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Complex addresses receive the additive ledger length Re. The addressed scaling is therefore " +
                    "the existing scalingLedger evaluated at the displacement address, retaining the ledger's " +
                    "semantic factor (Re(rho) - 1/2) and making the resulting scalar a quadratic displacement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-addressed-scaling"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.zeroAddressedScaling"),
                H("Zero-addressed scaling readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero address is fed to the existing scalingLedger with the additive real-part length. " +
                    "This is the scalar ledger displacement used by the selected second variation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-addressed-scaling-identity"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_scaling_eq"),
                H("Zero-addressed scaling is a squared displacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unfolding the mirror-antisymmetric address and the real-part length gives twice the square " +
                    "of the real displacement from the critical line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-addressed-variation-mirror"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_variation_mirror"),
                H("Mirror compatibility of addressed variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mirror reverses both the scaling entry and the antisymmetric address. Their product is " +
                    "therefore unchanged, and the selected even energy assigns equal local deficit to both members " +
                    "of a mirror pair. At a common address, the signed entries still cancel exactly by " +
                    "ZeroGeometry; the energy records the magnitude without mistaking cross-position cancellation " +
                    "for local balance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-to-deficit-measure"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.scalarToDeficitMeasure"),
                H("Scalar-to-measure embedding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonnegative scalar weight w at rho is embedded as ENNReal.ofReal(w) times the Dirac measure " +
                    "at rho. This is the canonical atomic inclusion: it changes codomain without changing the " +
                    "spectral address, and the nonnegativity theorem ensures that no signed mass is silently clipped."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mirror-pair-deficit-measure"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.mirrorPairDeficitMeasure"),
                H("Mirror-pair deficit measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A mirror pair is embedded by adding the two weighted Dirac atoms, one at each spectral address."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mirror-pair-deficit-measure-invariant"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_deficit_measure_invariant"),
                H("Mirror-pair measure compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two-point measure obtained by adding the two Dirac atoms is invariant under swapping the " +
                    "mirror pair. This respects the cancellation identity in ZeroGeometry while retaining the " +
                    "nonnegative second-order mass at each address."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-variation-is-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_nonneg"),
                H("The selected variation is nonnegative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defining Hessian identity is a nonnegative square, so every ledger displacement has " +
                    "nonnegative deficit energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-variation-is-even"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_neg"),
                H("The selected variation is even under reversal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing the signed ledger displacement leaves the squared second-order energy unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mirror-pair-zero-readout-compatibility"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_zero_readout_compatibility"),
                H("Signed cancellation and even energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every additive ledger and every common address, the mirror entries sum to zero while their " +
                    "selected second variations agree. This is the required compatibility law: reflection cancels " +
                    "the signed ledger reading, and the centered quadratic loss descends to the mirror orbit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-deficit-measure"),
                DeclarationHandle.Create("D5/S3/Weil/LedgerDeficitSecondVariation.zeroDeficitMeasure"),
                H("Zero-indexed deficit measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complete readout places the selected deficit weight at the zero's original spectral address."))),
                DescribeRole.Definition),
            Describe.Remark(
                DescribeId.Create("independent-semantic-justification"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation"),
                H("Independent semantic justification"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The choice is derived from the intrinsic ledger declarations only. " +
                        "scalingLedger length s a is (s.re - 1/2) times length a, so its signed value is " +
                        "the displacement from the critical line. half_density_reading_norm identifies the " +
                        "corresponding normalized norm as exp(-scalingLedger ...); hence the unitary locus is " +
                        "the norm value 1 at zero displacement. For a signed displacement d, introduce the " +
                        "dimensionless rate curve N_d(u) = exp(-d u). The Euclidean/Riemannian metric in the " +
                        "positive norm coordinate has squared distance (N_d(u) - 1)^2 from that unitary locus. " +
                        "Its Hessian at u = 0 is therefore the centered, nonnegative local energy, and no " +
                        "additional calibration constant is needed.")),
                    Paragraph(Text(
                        "This geometry selects ((N - 1)^2)''(0) among the listed candidates: log N is affine " +
                        "in u and has zero curvature, while N - 1 and N^2 - 1 are unsquared signed displacements " +
                        "whose values change sign under reversal and so are not centered nonnegative losses. " +
                        "Squaring before differentiating is additive across independent coordinates and even " +
                        "under d to -d, yielding the machine identity ledgerDeficitSecondVariation d = 2 d^2.")),
                    Paragraph(Text(
                        "The address rho - mirror(rho) is the canonical mirror-antisymmetric zero coordinate. " +
                        "mirror_reversal_spec reverses the addressed ledger entry, while the selected even " +
                        "energy is invariant; ZeroGeometry still supplies exact signed cancellation at a common " +
                        "address. Finally, scalarToDeficitMeasure embeds each nonnegative scalar as " +
                        "ENNReal.ofReal(w) times the Dirac measure at its spectral address, and the zeroDeficitMeasure " +
                        "readout uses the proven nonnegative weight. This argument was fixed before any toy " +
                        "comparison and does not use which candidate matches the W-B1 toy or any toy constants."))))
        )));
}
