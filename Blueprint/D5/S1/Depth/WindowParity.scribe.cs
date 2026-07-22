using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class WindowParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/WindowParity",
                "Prove the exact four-entry golden capacity and finite Witt parity law."),
            H("Golden Window Capacity and Parity"),
            Blocks(
                Paragraph(Text(
                    "This module proves the two exact algebraic clauses of the source remark. The attribution of cascade chirality remains unresolved because parity alone does not identify the source cascade dynamics. No empirical certificate or asymptotic claim follows from either finite identity.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("full-window-and-golden-capacity"),
                    DescribeKind.Theorem,
                    H("The full window has exact golden capacity four"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/WindowParity.full_window_and_golden_capacity")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The natural numbers below four are exactly zero, one, two, and three, so the full window contains each value once. Its cardinality agrees with the exact integer floor of the cubed golden ratio, proved from the quadratic golden identity and order bounds rather than decimal evaluation."))),
                    LatexStatement.Create(@"$$\left(\forall b\in\mathbb{N},\ b<4\Leftrightarrow b=0\lor b=1\lor b=2\lor b=3\right)\land\left|\left\{0,1,2,3\right\}\right|=4\land\left\lfloor\varphi^3\right\rfloor=4$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("witt-window-sum-parity"),
                    DescribeKind.Theorem,
                    H("Finite Witt alternation is exactly controlled by parity"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/WindowParity.witt_window_sum_parity")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every finite window length, the alternating geometric sum is zero exactly for even length and one exactly for odd length. Both converses are included, so the result records termination and the odd alternating remainder without a one-way weakening."))),
                    LatexStatement.Create(@"$$\begin{aligned}\sum_{j=0}^{L-1}(-1)^j=0&\Leftrightarrow 2\mid L,\\\sum_{j=0}^{L-1}(-1)^j=1&\Leftrightarrow\neg(2\mid L).\end{aligned}$$")))));
}
