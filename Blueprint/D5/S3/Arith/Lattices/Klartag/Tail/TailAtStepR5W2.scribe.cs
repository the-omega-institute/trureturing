using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailAtStepR5W2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail At Step R5W2"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail at step r5w2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "ChainRaw3", "Chain Raw3",
                "The raw datum with a terminal weight. ChainRaw2RW2 plus the single-time bound the count event needs.", DescribeRole.Definition),
            Node("claim-2", "profStep_le_horizon", "prof Step le horizon",
                "The terminal step's bound is below the horizon's, by monotonicity of profile in t.", DescribeRole.Theorem),
            Node("claim-3", "wProf", "w Prof",
                "The t-integrated profile bound, as the weight. ChainRaw2RW2.tail at it is le_refl.", DescribeRole.Definition),
            Node("claim-4", "wProfT", "w Prof T",
                "The terminal profile bound, as the weight. ChainRaw3.tailT at it is le_refl.", DescribeRole.Definition),
            Node("claim-5", "chainRaw3_of_raw2", "chain Raw3 of raw2",
                "The weight swap (route note). Any ChainRaw2RW2 becomes a ChainRaw3 whose two weights are the profile bounds themselves: every arithmetic field is carried over untouched and both tail fields are le_refl, so the record is g-free and chain-free.", DescribeRole.Definition),
            Node("claim-6", "integrable_profile_euclidean", "integrable profile euclidean",
                "Params.integrable for a single-time profile. integrable_radial_euclidean without the t-integral: bounded by 1/2, supported in closedBall 0 W.", DescribeRole.Theorem),
            Node("claim-7", "dom_of_tailT", "dom of tail T",
                "Params.dom for a single-time profile. dom_of_tail2 without the t-integral; the shift in profileAt is again exactly the cube radius √n/2.", DescribeRole.Theorem),
            Node("claim-8", "combW", "comb W",
                "The combined contact weight: A·w_int + B·w_T, in ℝ≥0∞.", DescribeRole.Definition),
            Node("claim-9", "combF", "comb F",
                "Its radial profile. The 4s of ChainRaw3.tail and ChainRaw3.tailT sit inside, so the second coefficient is 4·B; that is the b of Lemma43R3.radial_bound_combined_le.", DescribeRole.Definition),
            Node("claim-10", "C3", "C3",
                "The combined radial estimate uses the scaled sum of the integrated-contact coefficient and the terminal-contact coefficient.", DescribeRole.Definition),
            Node("claim-12", "combF_nonneg", "comb F nonneg",
                "combF is nonnegative.", DescribeRole.Theorem),
            Node("claim-13", "ofReal_comb_le", "of Real comb le",
                "The ℝ≥0∞ arithmetic of Params.dom for a sum of two weights, isolated so the record below does not carry it inline.", DescribeRole.Theorem),
            Node("claim-15", "paramsProducer3", "params Producer3",
                "paramsProducer3. Theorem2R3.ParamsProducerR2's five equalities, with ChainRaw3 in the binder and the combined weight in the fourth — all five are rfl on the record above.", DescribeRole.Theorem),
            Node("claim-16", "sums_split", "sums split",
                "The split, at a general §5 threshold. TerminalCount.sums_of_combined asks for ∑ < 1; the §5 output is ∑ < θ, so the coefficients passed to it are divided by θ, and the two admissibility facts become θ ≤ A·θ₁ and θ ≤ B·θ₂. That pair is scale-invariant in (A, B), which is why no normalisation of the combined weight is needed.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
