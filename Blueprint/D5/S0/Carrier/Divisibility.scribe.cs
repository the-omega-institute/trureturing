using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class DivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/Divisibility",
            "Golden-integer divisibility bounds the absolute value of the norm."),
        H("Golden Divisibility"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Divisibility"),
                Text(" exposes the standard normed-domain consequence of multiplicativity: if a golden integer divides a nonzero golden integer, then its absolute norm cannot be larger.")),
            new DocumentBlock.Describe(
                DescribeId.Create("divisor-norm-bound"),
                DescribeKind.Theorem,
                H("Divisor norm bound"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/Divisibility.norm_natAbs_le_of_dvd")),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Writing `y = x*z`, the hypothesis `y != 0` forces `z != 0`. The multiplicative norm identity rewrites `|N(y)|` as `|N(x)| * |N(z)|`, and `N(z) != 0` makes the second factor at least one."))),
                LatexStatement.Create(@"$\forall x,y\in\mathbb{Z}[\varphi],\ y\neq 0 \land x\mid y \Rightarrow \lvert\operatorname{norm}(x)\rvert\leq\lvert\operatorname{norm}(y)\rvert$")))));
}
