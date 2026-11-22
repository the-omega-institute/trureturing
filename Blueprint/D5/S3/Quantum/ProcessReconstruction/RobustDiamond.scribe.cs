using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class RobustDiamondDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/RobustDiamond";
    private static readonly LibraryNoteRef Bravyi = LibraryNoteRef.Create("D5/L/ProcessReconstruction/bravyi2026identitycheck");
    private static readonly LibraryNoteRef Huang = LibraryNoteRef.Create("D5/L/ProcessReconstruction/huang2024learning");
    private static readonly LibraryNoteRef Johnston = LibraryNoteRef.Create("D5/L/ProcessReconstruction/johnston2009computing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimension-independent stability in unhalved diamond distance from complete single-output unitary channel data.",
        H("Robust Local-Output Unitary Reconstruction"),
        Blocks(
            Paragraph(Text(
                "Let U and V be arbitrary unitaries on a finite tensor product of nonzero local "
                + "spaces. For every site i, trace out all other outputs. Both resulting channels "
                + "still take the full global input. Let δ be the sum over sites of the unhalved "
                + "diamond distances of these pairs, and let D be the unhalved diamond distance "
                + "between the global conjugation channels. Every distance permits arbitrary finite "
                + "ancillas on the input, with their identity action retained in the output.")),
            Describe.Lean(DescribeId.Create("small-sewing-error"),
                DeclarationHandle.Create(Module + ".diamond_le_sewing_of_lt_sqrt_three"),
                H("Coefficient one from a small doubled-unitary error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang, Johnston),
                Blocks(Paragraph(Text(
                    "For any finite nonzero basis and two unitaries, an operator-norm upper bound "
                    + "ε below √3 for the doubled-unitary difference also bounds D. A maximal "
                    + "spectral chord of the relative unitary gives a common spectral half-plane "
                    + "and hence a lower bound on every pure output overlap. The canonical "
                    + "pure-state reduction transfers the resulting upper bound to diamond distance."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("small-local-error"),
                DeclarationHandle.Create(Module + ".diamond_le_sum_localError_of_lt_sqrt_three"),
                H("Coefficient one for small complete local-output error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang, Johnston),
                Blocks(Paragraph(Text(
                    "If δ < √3, then D ≤ δ. The operator-norm step comes from the local SWAP "
                    + "comparison. The √3 threshold is sufficient for the spectral half-plane argument."))),
                DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("global-scaled-bound"),
                DeclarationHandle.Create(Module + ".diamond_le_min_scaled_sum_localError"),
                H("Global bound with the spectral conversion factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang, Johnston),
                Blocks(Paragraph(Text(
                    "For every δ, D ≤ min(2, (2/√3)δ). Below √3 use the coefficient-one "
                    + "estimate. At and above √3 use the universal distance bound of two. "
                    + "The factor 2/√3 is used here as an upper bound for the local-error "
                    + "sum formulation."))), DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("two-min-bound"),
                DeclarationHandle.Create(Module + ".diamond_le_two_min_one_sum_localError"),
                H("Clipped bound with coefficient two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang, Johnston),
                Blocks(Paragraph(Text(
                    "The same pair also obeys D ≤ 2 min(1, δ), by using the small-error result "
                    + "up to δ = 1 and the universal distance bound for δ ≥ 1."))),
                DescribeRole.Proposition))));
}
