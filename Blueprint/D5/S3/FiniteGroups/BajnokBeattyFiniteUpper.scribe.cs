using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyFiniteUpperDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed covers bound the actual order of every finite noncyclic abelian group.",
        H("Abstract finite noncyclic upper bounds"),
        Blocks(
            Describe.Lean(DescribeId.Create("bajnok-finite-upper-dichotomy"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyFiniteUpper.finite_noncyclic_upper_dichotomy"),
                H("The actual relation lattice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For an arbitrary finite additive commutative group G in any universe, a noncyclicity proof and a signed cover by a,b of natural radius s ≥ 3 yield a natural c ≥ 2. Either |G| ≤ 2s², or c is odd, c divides 2s+1, and 2|G| ≤ (2s+1)²−c². No distinctness, regularity or product normal form is assumed. The coefficient homomorphism from Z² is onto because of the cover; its quotient by its actual kernel is additively equivalent to G, so its actual index is |G|. Mathlib supplies classical Smith diagonal bases and two nonzero coefficients, without any ordered invariant-factor assertion. Coprimality would make their ZMod product cyclic, contradicting the hypothesis. Their gcd is at least two. Expanding each kernel vector in the bottom basis proves both original coordinates divisible by that gcd; this step does not confuse Smith coordinates with the coordinates of a,b. The public lattice_upper_bound then reuses the existing square-compression and scaled-index proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bajnok-finite-upper-prime"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyFiniteUpper.finite_noncyclic_upper_prime"),
                H("Prime 2s+1"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When 2s+1 is prime, every nontrivial common divisor c in the high-index branch equals 2s+1. The high bound then forces twice the positive group order to be at most zero. Thus |G| ≤ 2s²."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bajnok-finite-upper-composite"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyFiniteUpper.finite_noncyclic_upper_composite"),
                H("Composite 2s+1"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When 2s+1 is composite and p is its least prime factor, the exact conclusion in natural arithmetic is 2|G| ≤ (2s+1)²−p². In the low branch p² ≤ 2s+1 makes the baseline sufficient. In the high branch p ≤ c and hence p² ≤ c² give the correction. The proof establishes nonnegativity before returning to natural subtraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bajnok-finite-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyFiniteUpper.finite_noncyclic_upper"),
                H("The uniform upper endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every finite noncyclic abelian group with an arbitrary signed covering pair and s ≥ 3 has order at most 2s² when 2s+1 is prime, and satisfies twice the order at most (2s+1)² minus the least-prime-factor square otherwise. This is the abstract upper direction of Bajnok–Beatty arXiv:2406.04045v1 Conjecture 1.6. Matching lower constructions and assembly of the literal maximum are separate obligations. The Smith normal form machinery is classical; the formal transfer and estimate carry no claim of current literature novelty or publication priority."))), DescribeRole.Theorem))));
}
