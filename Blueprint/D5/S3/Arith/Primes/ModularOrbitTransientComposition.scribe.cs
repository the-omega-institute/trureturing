using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class ModularOrbitTransientCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact local modular transients and periods compose under the Chinese remainder constraint.",
        H("Combining modular orbit transients and periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("modular-orbit-factorwise-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_product_sequence"),
                H("Exact collision law for pairwise coprime factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two distinct indices collide modulo the product exactly when the earlier "
                    + "index is beyond every local transient and their lag is divisible by "
                    + "every local period. This combines transients by maximum and periods "
                    + "by least common multiple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("modular-orbit-sharp-tail-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_tail_period"),
                H("Sharp onset and all positive shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive shift preserves every reading from a chosen starting index "
                    + "if and only if that index is beyond the transient and the shift is "
                    + "a multiple of the period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("modular-orbit-exact-residue-count"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ModularOrbitTransientComposition.exact_residue_count"),
                H("The full residue image has transient plus period elements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite prefix consisting of the whole transient and one complete "
                    + "period represents all residues exactly once. The formal proof gives "
                    + "a bijection, not just an upper bound."))),
                DescribeRole.Theorem))));
}
