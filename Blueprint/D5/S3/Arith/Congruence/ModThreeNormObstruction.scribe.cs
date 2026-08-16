using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ModThreeNormObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer congruent to two modulo three is not a norm of the form x^2 + 3y^2.",
        H("The Mod-Three Quadratic Norm Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-m-minus-one-is-not-a-quadratic-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ModThreeNormObstruction."
                    + "three_mul_sub_one_not_quadratic_norm"),
                H("No number 3m - 1 is an x^2 + 3y^2 norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"),
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("x"), Caret, Grp(D(2)), Plus, D(3), F.Id("y"), Caret, Grp(D(2)),
                    Sp, Neq, Sp, D(3), F.Id("m"), Minus, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all integers m, x, and y, the equality x^2 + 3y^2 = 3m - 1 is "
                        + "impossible. Reduction modulo three kills both terms carrying a factor "
                        + "three, leaving x^2 = 2 in ZMod 3, while a square modulo three is only "
                        + "zero or one.")),
                    Paragraph(Text(
                        "The repository was searched before construction. The lower-layer theorem "
                        + "ZeroOrbitCongruence.eisenstein_norm_mod_three supplies the square-residue "
                        + "dichotomy by specialization at its second variable zero, and is applied "
                        + "directly. Pinned Mathlib text search found only packaged modulo-four square "
                        + "obstructions, and the exact Loogle query for a square in ZMod 3 unequal to "
                        + "two returned no declaration.")),
                    Paragraph(Text(
                        "This node closes only the explicit claim in appendix E.52 that an integer in "
                        + "the residue class two modulo three cannot be such a quadratic norm. It does "
                        + "not formalize the full Markov-geodesic avoidance theorem, the trace reduction, "
                        + "the crossing-spectrum lower bound, or the numerical certificate."))),
                DescribeRole.Theorem))));
}
