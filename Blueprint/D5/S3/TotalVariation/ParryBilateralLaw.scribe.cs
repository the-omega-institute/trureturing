using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryBilateralLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryBilateralLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bilateral Parry source and its signed path law.",
        H("The bilateral Parry source and its signed path law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parrybilaterallaw-bilateral-reset-coding"),
                DeclarationHandle.Create(Prefix + "bilateral_reset_coding"),
                H("Measurable bilateral reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix k >= 2. A relation path is a function r from the integers to Bool with "
                        + "a zero in every block of k consecutive bits. Its suffix j_t counts the true "
                        + "bits immediately before t. The nearest preceding zero exists and gives "
                        + "0 <= j_t < k; specifically r_(t-j_t-1) is false and the j_t bits after it "
                        + "are true. Starting with a sign b at zero, finite XOR of the complemented "
                        + "relation bits reconstructs a_t in each time direction.")),
                    Paragraph(Text(
                        "The map (b,r) to the path (a_t,j_t) is a measurable equivalence onto the "
                        + "bilateral paths whose every edge has positive mass under "
                        + "TwistedResetPaths.kernel k (parryParameter k). Its inverse reads a_0 "
                        + "and r_t = not (a_t xor a_(t+1)). The coding intertwines the path shift "
                        + "with (b,r) to (b xor not r_0, relationShift r). The suffix characterization "
                        + "and inverse hold for every supported path, including negative times."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parrybilaterallaw-bilateral-parry-law"),
                DeclarationHandle.Create(Prefix + "bilateral_parry_law"),
                H("The actual stationary source and joint law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every k >= 2 there exist a stationary probability measure mu on the "
                        + "actual relation space, a stationary probability measure nu on integer-indexed "
                        + "signed state paths, and a measurable coding with all the preceding properties. "
                        + "Writing p = parryParameter k, h_j = suffixWeight k p j and S = normalizer k, "
                        + "the suffix stationary mass is p^j h_j / S. Its transition kernel is p/h_j "
                        + "to zero, p h_(j+1)/h_j to j+1 when that state exists, and zero otherwise. "
                        + "At every integer origin, every finite suffix cylinder under mu has exactly "
                        + "the product of this initial mass and these transition probabilities. "
                        + "The suffix is the preceding true run specified by the coding, so this "
                        + "identifies mu with the forbidden-run Parry source.")),
                    Paragraph(Text(
                        "The image of fairAnchor times mu under the coding is exactly nu as a measure. "
                        + "For every integer ell, natural m and word w of m+1 signed states, its "
                        + "cylinder mass is ofReal(parryLaw k (w_0) times the product, over i < m, "
                        + "of kernel k p (w_i) (w_(i+1))). This includes m=0 and words with zero "
                        + "transition mass. The anchor is fair and independent of the entire relation "
                        + "path, not merely of a suffix coordinate or a finite window.")),
                    Paragraph(Text(
                        "The construction first extends the compatible signed Markov masses on "
                        + "centered finite blocks using the existing inverse-limit probability theorem, "
                        + "and then identifies coherent blocks with paths on the integers. Sign-complement "
                        + "symmetry and uniqueness of that extension give equal masses to the two "
                        + "anchor slices over every measurable relation event; these slices establish "
                        + "the product disintegration. Summing the signed word masses over signs "
                        + "gives the source suffix cylinders. Shift invariance follows from the "
                        + "same finite-dimensional characterization. This result supplies the law "
                        + "identification; mixing and measurable-section obstructions require further theorems."))),
                DescribeRole.Theorem))));
}
