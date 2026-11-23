using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class SmallGCDDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/SmallGCD.";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/Semigroups/benfieldlippard2025positivepowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the odd-exponent estimate, the shifts from the first floor(p/3) bases have gcd one.",
        H("The gcd of small shifted powers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-generators"),
                DeclarationHandle.Create(Prefix + "smallGenerators"),
                H("Shifted powers with bounded bases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text(
                    "For positive bases at most m, collect the shifted powers a^k−1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smallgcd"),
                DeclarationHandle.Create(Prefix + "small_gcd"),
                H("The gcd of small shifted powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text(
                    "A prime divisor common to the shifts would force all the small bases to be kth roots of unity. For a modulus up to the square of the base cutoff, an integer quotient and remainder force 1 = −1. Above that square, the products of powers of two and small odd bases give more distinct roots than the degree."))),
                DescribeRole.Theorem)
        )));
}
