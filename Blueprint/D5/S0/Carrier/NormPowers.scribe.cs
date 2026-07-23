using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class NormPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/NormPowers",
            "The golden norm carries natural powers to integer powers."),
        H("Golden Norm Powers"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("norm-powers"),
                DescribeKind.Theorem,
                H("Norm of a natural power"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/NormPowers.norm_pow")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The existing norm is packaged as a monoid homomorphism from `GoldenInt` to `Int`. Applying its standard power law gives the exact identity for every golden integer and every natural exponent, with no extra algebraic assumptions."))),
                LatexStatement.Create(@"$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n$$")))));
}
