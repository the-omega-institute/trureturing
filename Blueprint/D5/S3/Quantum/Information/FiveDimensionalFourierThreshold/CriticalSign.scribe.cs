using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class CriticalSignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the proposed sharp cutoff every compatible sign mask of the ten Born rows has five entries and belongs to the critical pair-product class.",
        H("Critical sign masks at the sharp score cutoff"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-sign-compatible"),
                DeclarationHandle.Create(Prefix + "SignCompatible"), H("Compatible sign choices, including ties"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For outcome tables p and q a compatible mask contains only rows with q ≤ p, and its complement contains only rows with p ≤ q. Either choice is admissible at a tied row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-sign-harmonic-bound"),
                DeclarationHandle.Create(Prefix + "harmonicOverlap_ge_sign_mask"), H("Baseline and complementary-row harmonic mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative tables with first-law total mass two, the harmonic overlap is at least half the sum of the minima. If a complementary set of rows satisfies 0.09(p+q) ≤ q−p and p+q > 0, the overlap is at least (2 − maskMass p s + maskMass q s)/2 plus 0.045 times the first-law mass on that set. The baseline estimate includes a common zero row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sign-critical-pairs"),
                DeclarationHandle.Create(Prefix + "CriticalPairProduct"), H("The critical pair-product class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A pair of two-element masks in the two bases belongs to this class if the product of their ordered differences in the residue field modulo five is 1 or −1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-sign-critical-five"),
                DeclarationHandle.Create(Prefix + "CriticalFiveMask"), H("Critical masks of size five"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Either the computational pair and the omitted Fourier pair are critical, or the omitted computational pair and the Fourier pair are critical."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-sign-rank-four-exclusion"),
                DeclarationHandle.Create(Prefix + "rankFour_overlap_gt_sharpD"), H("Strict harmonic deficit on the four-row tails"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the sign-mask mass difference is at most 1 + σ and on a complementary tail the first-law square-root mass exceeds 0.228, each first-law amplitude is below 0.305, and the second amplitude exceeds the first by 0.029, the harmonic overlap strictly exceeds (3 − √5)/10. Squaring the amplitude comparison gives the required relative difference 0.09. The exact rational bounds budget both spectral deficits jointly in the critical rank-four application."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sign-mask-at-cutoff"),
                DeclarationHandle.Create(Prefix + "critical_sign_mask_at_cutoff"), H("Every compatible sign mask is critical at the cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any pair of complex unit vectors with combined score at least (14 + 2√5)/5 has a sign-mask mass difference at least 2c², where c = √((7 + √5)/10). A noncritical mask of size at most four has mass difference at most 1 + √(3/5), and a noncritical five-row mask has mass difference at most 2√(4/5). Both are strictly below 2c². The critical rank-four mask is excluded by the harmonic tail estimate. Complement and simultaneous exchange of the two states reduces larger masks to the smaller side, proving the claim for every tie assignment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sign-no-ties"),
                DeclarationHandle.Create(Prefix + "fiveLaw_ne_at_cutoff"), H("No tied row at the closed cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the cutoff regime the two Born probabilities are unequal in every computational and Fourier row. Inserting a tied row into the strict positive sign mask would give a second compatible mask of different cardinality, contradicting the requirement that both have five entries."))), DescribeRole.Theorem)),
        []));
}
