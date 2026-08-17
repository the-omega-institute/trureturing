using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ChannelFidelityBridgeDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite excitation-exchange permutation gives a unitary, a Kraus family, and an exact bridge from entanglement fidelity to the frozen nearest-neighbour quadratic form.",
        H("Finite Channel-to-Fidelity Bridge"),
        Blocks(
            Paragraph(Text(
                "The system has two basis states and the reference has N levels. The joint "
                + "basis permutation exchanges one excitation between them whenever the "
                + "reference is away from the corresponding boundary, and fixes the two "
                + "unmatched boundary vectors. All matrices and sums in this document are "
                + "finite-dimensional.")),
            Describe.Lean(
                DescribeId.Create("the-excitation-exchange-matrix-is-unitary"),
                DeclarationHandle.Create(LeanPrefix + "exchange_unitary_is_unitary"),
                H("The excitation-exchange matrix is unitary"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("U"), F.Caret, F.Grp(F.Star), F.Sp,
                    F.Id("U"), F.Sp, F.Eq, F.Sp, F.Id("I")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exchange matrix is the permutation matrix of an involution on the "
                    + "joint computational basis. Mathlib's conjugate-transpose and "
                    + "permutation-matrix multiplication identities therefore reduce the "
                    + "unitarity law to the inverse law of that permutation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exchange-preserves-total-excitation"),
                DeclarationHandle.Create(
                    LeanPrefix + "exchange_basis_preserves_total_excitation"),
                H("Exchange preserves total excitation"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("n"), F.Open, F.Id("exchange"), F.Open, F.Id("x"), F.Close,
                    F.Close, F.Sp, F.Eq, F.Sp,
                    F.Id("n"), F.Open, F.Id("x"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an interior transition the system excitation changes by one while the "
                    + "reference excitation changes by the opposite amount. At an unmatched "
                    + "boundary the basis label is fixed. The total grading is consequently "
                    + "unchanged in every branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-reduced-system-map-is-a-finite-kraus-sum"),
                DeclarationHandle.Create(LeanPrefix + "exchangeChannel"),
                H("The reduced system map is a finite Kraus sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Projecting the reference output onto each level r gives one matrix K_r. "
                    + "The reduced system map sends rho to the finite sum of K_r rho K_r star. "
                    + "This module introduces only this concrete family and does not add a "
                    + "general channel library."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("entanglement-fidelity-is-the-frozen-quadratic-form"),
                DeclarationHandle.Create(
                    LeanPrefix + "entanglement_fidelity_eq_nearest_neighbor_quadratic"),
                H("Entanglement fidelity is the frozen quadratic form"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
                    F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")),
                    F.Open, F.Id("c"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Entanglement fidelity is defined by the finite trace expression one "
                    + "quarter times the sum of the squared trace magnitudes against the ideal "
                    + "bit flip. Computing the two off-diagonal Kraus entries leaves exactly "
                    + "the two zero-boundary neighbouring reference amplitudes. The resulting "
                    + "sum is definitionally the existing nearestNeighborQuadratic; that "
                    + "quadratic is imported and is not redefined here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entanglement-fidelity-is-the-squared-averaging-norm"),
                DeclarationHandle.Create(
                    LeanPrefix + "entanglement_fidelity_eq_average_norm_sq"),
                H("Entanglement fidelity is the squared averaging norm"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
                    F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
                    F.Lvert, F.Sp, F.Id("J"), F.Id("c"), F.Rvert,
                    F.Underscore, F.Grp(F.D(2)), F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here J is zero-boundary nearest-neighbour averaging. This restates the "
                    + "same compiled bridge as a squared Euclidean norm and is the exact input "
                    + "needed by the finite path-spectrum module."))),
                DescribeRole.Theorem))));
}
