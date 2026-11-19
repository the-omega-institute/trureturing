using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class BinaryEndpointLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/BinaryEndpointLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformity of finite binary images of independent endpoint choices.",
        H("When independent endpoint choices give a uniform binary image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-endpoint-uniformity"),
                DeclarationHandle.Create(Prefix + "mass_eq_uniform_iff_span"),
                H("The fair generators determine uniformity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a finite vector space over the field with two elements. " +
                        "Choose a vector a(i) in V and a complex number p(i) for each index i " +
                        "in a finite set. Give the choice of a(i) weight p(i) and the choice " +
                        "of zero weight 1-p(i). Multiply these weights across indices. " +
                        "For each v in V, sum the resulting weights of all choices whose " +
                        "vectors add to v.")),
                    Paragraph(Text(
                        "The resulting function is constant with value 1 divided by the " +
                        "cardinality of V exactly when the vectors a(i) for which p(i)=1/2 " +
                        "span V over the field with two elements. For real parameters in " +
                        "the unit interval this is the law of a sum of independent " +
                        "Bernoulli choices. Empty index sets, deterministic choices and " +
                        "the zero-dimensional space are included.")),
                    Paragraph(Text(
                        "Each character moment factors into one term per index. " +
                        "A nontrivial character picks up a zero factor exactly when it " +
                        "takes value -1 on a fair generator. If the fair vectors span a " +
                        "proper subspace, a nonzero linear functional vanishing on that " +
                        "subspace supplies a character whose moment stays nonzero. " +
                        "If the fair vectors span V, all nontrivial moments vanish. The " +
                        "finite character basis then identifies the mass function."))),
                DescribeRole.Theorem))));
}
