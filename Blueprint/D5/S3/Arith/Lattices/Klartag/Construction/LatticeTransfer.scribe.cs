using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class LatticeTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Lattice Transfer"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate lattice transfer to the stochastic ellipsoid construction.")),
            Node("claim-1", "zero_mem_ellipsoid", "zero mem ellipsoid",
                "The origin is in every ellipsoid.", DescribeRole.Theorem),
            Node("claim-2", "mem_ellipsoid_congr", "mem ellipsoid congr",
                "The congruence A ↦ Bᵀ A B pulls the ellipsoid back along B.", DescribeRole.Theorem),
            Node("claim-3", "det_congr", "det congr",
                "det (Bᵀ A B) = det(B)² det(A).", DescribeRole.Theorem),
            Node("claim-4", "congr_factor", "congr factor",
                "The congruence factor transports: S' = B⁻¹ S works for A' = Bᵀ A B.", DescribeRole.Theorem),
            Node("claim-5", "integerPoints_eq_zero", "integer Points eq zero",
                "H10 — the lattice transfer. If E_A contains no non-zero point of the lattice B(ℤⁿ), then the congruent ellipsoid E_{BᵀAB} contains no non-zero point of ℤⁿ. This is ChainEllipsoid.klartag_of_chain's last conjunct.", DescribeRole.Theorem),
            Node("claim-6", "chain_hyp_of_transfer", "chain hyp of transfer",
                "H10, packaged for klartag_of_chain. From an L-free ellipsoid in the lattice frame (L = B(ℤⁿ)) to the hypothesis body of ChainEllipsoid.klartag_of_chain in the integer frame.", DescribeRole.Theorem),
            Node("claim-7", "exists_basisMatrix", "exists basis Matrix",
                "The basis matrix. Every ℤ-lattice of full rank in Fin n → ℝ is B(ℤⁿ) for an invertible real matrix B. Stated for an arbitrary lattice (rule 7), not for Construction A: D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA.latR carries the two instances, so this applies to it directly.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
