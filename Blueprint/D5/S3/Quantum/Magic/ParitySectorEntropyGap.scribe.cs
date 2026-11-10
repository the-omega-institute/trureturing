using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ParitySectorEntropyGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ParitySectorEntropyGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/cepollaro2025stabilizer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-form extrinsic fourth-moment scores and four-branch positive average linear stabilizer-entropy gaps of the even and odd qudit parity sectors for every odd dimension at least three, small-dimension evaluations, and comparison against the random-subspace average when three does not divide the dimension.",
        H("Extrinsic terms and positive stabilizer-entropy gaps of the parity sectors"),
        Blocks(
            Node("paritysectorentropygap-even-extrinsic-formula-definition",
                "Closed-form even-sector extrinsic score", "evenExtrinsicFormula",
                "For a natural dimension d, evenExtrinsicFormula(d) equals 4 / (d + 3) when 3 does not divide d, and 4 / (d + 3) + 64 / ((d + 1)(d + 3)(d + 5)(d + 7)) when 3 divides d.",
                DescribeRole.Definition),
            Node("paritysectorentropygap-odd-extrinsic-formula-definition",
                "Closed-form odd-sector extrinsic score", "oddExtrinsicFormula",
                "For a natural dimension d, oddExtrinsicFormula(d) equals 4 / (d + 3) when 3 does not divide d, and 4 / (d + 3) - 64 / ((d - 1)(d + 1)(d + 3)(d + 5)) when 3 divides d.",
                DescribeRole.Definition),
            Node("paritysectorentropygap-even-gap-formula-definition",
                "Four-branch closed-form even-sector gap", "evenGapFormula",
                "For a natural dimension d, evenGapFormula(d) gives the rational closed form of Delta M(E_d) across the four residue classes determined by d mod 4 in {1, 3} and divisibility by 3: 2(d - 1) / ((d + 3)(d + 5)) for d = 1 mod 4 with 3 not dividing d; 2(d^2 + 4 d - 13) / ((d + 1)(d + 5)(d + 7)) for d = 1 mod 4 with 3 dividing d; 2(d + 1) / ((d + 3)(d + 7)) for d = 3 mod 4 with 3 not dividing d; and 2(d^3 + 7 d^2 + 11 d - 27) / ((d + 1)(d + 3)(d + 5)(d + 7)) for d = 3 mod 4 with 3 dividing d.",
                DescribeRole.Definition),
            Node("paritysectorentropygap-odd-gap-formula-definition",
                "Four-branch closed-form odd-sector gap", "oddGapFormula",
                "For a natural dimension d, oddGapFormula(d) gives the rational closed form of Delta M(O_d) across the four residue classes determined by d mod 4 in {1, 3} and divisibility by 3: 2 / (d + 3) for d = 3 mod 4 with 3 not dividing d; 2(d^3 + 5 d^2 - d + 27) / ((d - 1)(d + 1)(d + 3)(d + 5)) for d = 3 mod 4 with 3 dividing d; 2(d^2 + 6 d + 17) / ((d + 1)(d + 3)(d + 5)) for d = 1 mod 4 with 3 not dividing d; and 2(d^2 + 2 d + 5) / ((d - 1)(d + 1)(d + 5)) for d = 1 mod 4 with 3 dividing d.",
                DescribeRole.Definition),
            Node("paritysectorentropygap-parity-sector-extrinsic-terms-theorem",
                "Extrinsic fourth-moment terms of the even and odd parity sectors",
                "parity_sector_extrinsic_terms",
                "For every odd dimension d >= 3, the number N_3 of nonzero phase-space labels in (Z / dZ)^2 of order 3 equals 8 when 3 divides d (forming the punctured 3-torsion subgroup ((d / 3)(Z / dZ))^2 \\ {(0, 0)}) and 0 otherwise. Summing d^{-1} sum_a labelFourthMoment(V, a) over the origin, the d^2 - 1 - N_3 generic nonzero labels, and the N_3 order-3 labels establishes extrinsicScore(E) = evenExtrinsicFormula(d) for every isometric embedding E of E_d and extrinsicScore(E) = oddExtrinsicFormula(d) for every isometric embedding E of O_d. In particular, at d = 3 the extrinsic scores evaluate to X(E_3) = 7 / 10 and X(O_3) = 1 / 2.",
                DescribeRole.Theorem),
            Node("paritysectorentropygap-parity-sector-gaps-and-positivity-theorem",
                "Four-branch parity-sector stabilizer-entropy gaps and universal positivity",
                "parity_sector_gaps_and_positivity",
                "For every odd dimension d >= 3, the even sector dimension k_{E_d} = (d + 1) / 2 is odd if and only if d = 1 mod 4, while the odd sector dimension k_{O_d} = (d - 1) / 2 is odd if and only if d = 3 mod 4. Subtracting the extrinsic formulas from the odd-k and even-k single-qudit intrinsic terms establishes aseGap(E) = evenGapFormula(d) for every isometric embedding E of E_d and aseGap(E) = oddGapFormula(d) for every isometric embedding E of O_d, matching each of the four explicit rational branch expressions and satisfying Delta M(E_d) > 0 and Delta M(O_d) > 0 for every odd d >= 3. In small odd dimensions d in {3, 5, 7, 9}, the formulas evaluate to Delta M(E_3) = 1 / 10, Delta M(O_3) = 1 / 2, Delta M(E_5) = 1 / 10, Delta M(O_5) = 3 / 10, Delta M(E_7) = 4 / 35, Delta M(O_7) = 1 / 5, Delta M(E_9) = 13 / 140, and Delta M(O_9) = 13 / 70; for O_3, k_{O_3} = 1 with I(1) = 1, so Delta M(O_3) = 1 / 2 equals the pure-state linear stabilizer entropy of the unique normalized odd qutrit state (|1> - |2>) / sqrt(2).",
                DescribeRole.Theorem),
            Node("paritysectorentropygap-parity-sector-whole-space-comparison-theorem",
                "Comparison of parity-sector extrinsic scores and gaps against the whole-space average",
                "parity_sector_whole_space_comparison",
                "For every odd dimension d >= 3 not divisible by 3, both parity sectors have extrinsic score 4 / (d + 3), which strictly exceeds the ambient odd-dimension intrinsic term intrinsicTerm(d) = 3 / (d + 2) because 4(d + 2) - 3(d + 3) = d - 1 > 0. Since the Haar average of the extrinsic score over all k-dimensional subspaces of C^d equals intrinsicTerm(d) = 3 / (d + 2), both parity sectors have extrinsic score strictly above the random-subspace average and consequently have average stabilizer-entropy gap strictly below the random-subspace average gap I(k) - 3 / (d + 2) of the same sector dimension k.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
