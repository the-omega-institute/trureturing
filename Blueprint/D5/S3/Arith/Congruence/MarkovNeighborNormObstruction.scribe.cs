using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class MarkovNeighborNormObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The neighboring Markov factors cannot multiply to a norm of the form x^2 + 3y^2.",
        H("The Markov Neighbor Norm Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("markov-neighbor-product-is-not-a-quadratic-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/MarkovNeighborNormObstruction."
                    + "markov_neighbor_product_not_quadratic_norm"),
                H("The neighboring factors do not form a quadratic norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("mu"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"),
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("x"), Caret, Grp(D(2)), Plus, D(3), F.Id("y"), Caret, Grp(D(2)),
                    Sp, Neq, Sp,
                    Open, D(3), F.Id("mu"), Minus, D(1), Close,
                    Open, D(3), F.Id("mu"), Plus, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all integers mu, x, and y, the product (3mu - 1)(3mu + 1) cannot "
                        + "equal x^2 + 3y^2. The product is 9mu^2 - 1, hence has the form "
                        + "3m - 1 with m = 3mu^2.")),
                    Paragraph(Text(
                        "The proof applies the existing repository theorem "
                        + "ModThreeNormObstruction.three_mul_sub_one_not_quadratic_norm directly "
                        + "after the factor identity. Pinned Mathlib source search and two skill "
                        + "searches found no exact theorem. Online Loogle returned zero "
                        + "declarations for both the integer norm obstruction and its "
                        + "square-modulo-three core.")),
                    Paragraph(Text(
                        "This node closes only the even-branch arithmetic sentence in appendix "
                        + "E.52: the displayed neighboring-factor product is excluded by the "
                        + "modulo-three norm obstruction. It does not formalize the full "
                        + "Markov-geodesic avoidance theorem, the crossing-spectrum lower bound, "
                        + "or either numerical census."))),
                DescribeRole.Theorem))));
}
