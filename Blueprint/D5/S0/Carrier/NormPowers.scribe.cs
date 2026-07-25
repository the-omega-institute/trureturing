using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class NormPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/NormPowers",
            "The golden norm preserves natural powers through its monoid homomorphism."),
        H("Norm Powers"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("golden-norm-power-law"),
                DescribeKind.Theorem,
                H("Golden norm power law"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/NormPowers.norm_pow")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The multiplicative norm has already been packaged as `normMonoidHom`, so the natural-power law follows from the generic power preservation law for monoid homomorphisms. This generalizes the existing `phi` power computation without introducing new coordinate algebra."))),
                LatexStatement.Create(@"$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n.$$")))));
}
