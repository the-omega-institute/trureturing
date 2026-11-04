using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyAllRegimesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original four-clause classification holds for every positive k and s.",
        H("The original Bajnok–Beatty Conjecture 4.1"),
        Blocks(Describe.Lean(
            DescribeId.Create("bajnok-beatty-original-full-iff"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyAllRegimes.result"),
            H("Two-generator signed radius: all regimes"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For positive integers k and s, the group ZMod 2 × ZMod (2k) admits two distinct elements whose signed integer combinations of coefficient absolute-value sum at most s cover every group element exactly when at least one of these four clauses holds: s is odd and 2k ≤ s² − 1; s is even and 2k ≤ s² − s; s is congruent to zero modulo four, k is even, and s² − s < 2k ≤ s²; or s is congruent to two modulo four, k is congruent to two modulo four, and s² − s < 2k ≤ s². The quantifiers allow arbitrary generating pairs; there is no assumption on their first coordinates. The doubled inequalities express the rational bounds in the original statement without integer division.")),
                Paragraph(Text(
                    "The order bound and the odd and even low regimes are the known Theorems 4.2–4.4 of Bajnok and Beatty, arXiv:2406.04045v1. Their formal proofs use exact square representatives of the relation quotient, integer-cylinder covers with consecutive coefficients, and balanced modular lifts. They carry no claim of new mathematics.")),
                Paragraph(Text(
                    "In the remaining even top strip, the proof uses the existing arbitrary-pair necessity theorem and the existing uniform sufficient skew-lattice family. Necessity forces k to be even and, when s is congruent to two modulo four, k to be congruent to two modulo four. Sufficiency sets t = s/2 and j = t² − k/2 and applies the proved family. The boundary t = 1 is included, and every positive k is excluded when s = 1.")),
                Paragraph(Text(
                    "This is a formal result for the literal original arXiv v1 conjecture. No claim about mathematical priority or the status of later publications follows; later versions are outside the source comparison."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bajnok-beatty-original-conjecture-4-1"),
                ResolutionKind.Proved)))));
}
