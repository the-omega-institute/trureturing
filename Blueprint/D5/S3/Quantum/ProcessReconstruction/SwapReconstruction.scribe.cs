using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class SwapReconstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/SwapReconstruction";
    private static readonly LibraryNoteRef Huang = LibraryNoteRef.Create("D5/L/ProcessReconstruction/huang2024learning");
    private static readonly LibraryNoteRef Arrighi = LibraryNoteRef.Create("D5/L/ProcessReconstruction/arrighi2011unitarity");
    private static readonly LibraryNoteRef Schumacher = LibraryNoteRef.Create("D5/L/ProcessReconstruction/schumacher2004reversible");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete single-output channel distances control the doubled unitary and determine the global conjugation when they vanish.",
        H("Finite Local SWAP Reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("site-channel"),
                DeclarationHandle.Create(Module + ".siteChannel"),
                H("Full-input channel with one output site"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each site has its own finite basis type. For site i, keep just output i after "
                    + "conjugation by the unitary on the entire finite tensor product. The input "
                    + "domain remains the entire tensor product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-swap-sewing-bound"),
                DeclarationHandle.Create(Module + ".swap_sewing_opNorm_le"),
                H("Operator-norm control of the doubled unitary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Huang, Arrighi),
                Blocks(
                    Paragraph(Text(
                        "For any two unitaries U and V on the same tensor product, the operator "
                        + "norm of the difference between U† ⊗ U and V† ⊗ V is at most the sum "
                        + "of the unhalved diamond distances of their single-output channels. Each "
                        + "distance permits an arbitrary finite reference alongside the global input.")),
                    Paragraph(Text(
                        "Trace duality bounds the difference of the two conjugated local swaps "
                        + "site by site. Telescoping their products and multiplying by the full "
                        + "swap gives the doubled-unitary estimate. The conjugated SWAP construction "
                        + "is related to Huang et al., arXiv:2401.10095v1, Eq. (6), Remark 5 "
                        + "Eq. (109) and §5.2.2 Lemma 9, and to Arrighi, Nesme and Werner, "
                        + "arXiv:0711.3975v3, §IV Theorem 1. Lemma 9 uses Heisenberg Pauli "
                        + "errors. The estimate here uses complete reduced-channel norms."))),
                DescribeRole.Proposition),
            Describe.Lean(DescribeId.Create("exact-site-channel-uniqueness"),
                DeclarationHandle.Create(Module + ".conjugation_eq_of_siteChannel_eq"),
                H("Exact uniqueness from all one-site output channels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Schumacher),
                Blocks(Paragraph(Text(
                    "Equality of all full-input single-output channels forces equality of the "
                    + "global conjugation channels. The proof first makes the doubled-unitary "
                    + "difference vanish, then compares the coefficients of the two conjugations "
                    + "on every global matrix. Schumacher and Werner, quant-ph/0405174v1, §I "
                    + "and Lemma 2(1), give the corresponding uniqueness principle for "
                    + "homomorphisms specified by their local action."))), DescribeRole.Proposition))));
}
