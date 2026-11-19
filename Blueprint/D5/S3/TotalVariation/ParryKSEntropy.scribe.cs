using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryKSEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Metric entropy of the actual bilateral forbidden-run shift.",
        H("The Parry law attains the entropy bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("bilateral-parry-ks-entropy"),
            DeclarationHandle.Create("D5/S3/TotalVariation/ParryKSEntropy.bilateral_parry_entropy"),
            H("Maximum Kolmogorov–Sinai entropy of the bilateral Parry shift"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every k at least two, there exist a bilateral coding and a shift-invariant "
                    + "probability on the unsigned relation space with the stationary Parry suffix "
                    + "cylinders at every integer origin. Its full Kolmogorov–Sinai entropy is "
                    + "minus log p, with p the reciprocal Parry root. Every probability preserved "
                    + "by the same shift has Kolmogorov–Sinai entropy at most minus log p.")),
                Paragraph(Text(
                    "On each realized suffix word, the logarithm of its reference mass is the "
                    + "number of transitions times log p, plus terms from the first and last "
                    + "suffix. Those terms are uniformly bounded because the suffix alphabet is "
                    + "finite. Gibbs' inequality bounds any competitor's block entropy by its "
                    + "cross entropy against that reference. Taking the block length to infinity "
                    + "removes the endpoint terms. The reference law attains the bound by the "
                    + "corresponding lower estimate on its own block entropy.")),
                Paragraph(Text(
                    "Reading the suffix at successively earlier origins gives increasing "
                    + "forward-generated sigma algebras. Their supremum contains every Boolean "
                    + "coordinate because the next suffix is zero exactly at a false bit. "
                    + "Stationarity gives these shifted suffix partitions equal entropy rates, "
                    + "so their common rate is the full Kolmogorov–Sinai entropy."))),
            DescribeRole.Theorem))));
}
