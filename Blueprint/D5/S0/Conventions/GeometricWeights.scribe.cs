using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class GeometricWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/GeometricWeights",
            "No nonzero rational rescaling of geometric weights matches every singleton W weight."),
        H("Geometric Weights No-Go"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("geometric-weights-do-not-match-singleton-w-weights"),
                DescribeKind.Theorem,
                H("Geometric weights do not match singleton W weights"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Conventions/GeometricWeights."
                    + "no_geometric_weights_match_zeckendorf_singletons")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The W-digit convention defines wValue k as fib(k+2), so singleton bits have "
                    + "weights 1, 2, 3 at indices 0, 1, 2. The first two equations force the "
                    + "geometric ratio to be 2, while the third requires its square to be 3; "
                    + "the nonzero scale excludes cancellation."))),
                LatexStatement.Create(
                    @"$\neg\exists\,w_1,\Lambda,c\in\mathbb{Q},\ c\neq0:\ "
                    + @"w_1\Lambda^k=cF_{k+2}\ \text{for every }k\ge0.$")))));
}
