using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class ComplexityDensityExchangeRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive limiting complexity densities recover the entropy exchange rate.",
        H("Complexity Density Exchange Rate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complexity-density-ratio-tends-to-entropy-ratio"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/ComplexityDensityExchangeRate."
                    + "complexity_density_ratio_tendsto_entropy_ratio"),
                H("The density quotient tends to the entropy quotient"),
                StatementSource.FromAuthor(Equal(
                    Call("limitAlong", Id("l"),
                        Call("ratio",
                            Call("density1", Id("index")),
                            Call("density2", Id("index")))),
                    Call("ratio", Id("h1"), Id("h2")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the two complexity-density functions converge along the same "
                        + "filter to the positive tower entropies h1 and h2. Their quotient then "
                        + "converges to h1 divided by h2, which is the claimed height exchange rate.")),
                    Paragraph(Text(
                        "The source statement invokes Brudno's theorem to supply the two "
                        + "complexity-density limits. This formalization isolates the independent "
                        + "column-reduction step conditionally on those limits; it does not claim a "
                        + "formalization of Kolmogorov complexity or Brudno's theorem.")),
                    Paragraph(Text(
                        "Both entropies are explicitly positive, preserving the source's "
                        + "positive-entropy regime. In particular h2 is nonzero, avoiding Lean's "
                        + "totalized division-by-zero case. Pinned Mathlib's Filter.Tendsto.div is "
                        + "an exact match and is applied directly."))),
                DescribeRole.Theorem)),
        []));
}
