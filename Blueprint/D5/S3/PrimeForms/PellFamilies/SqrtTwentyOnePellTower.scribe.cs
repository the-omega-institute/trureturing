using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.PellFamilies;

internal sealed class SqrtTwentyOnePellTowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The norm-one fundamental unit preserves the Pell conic of discriminant 21.",
        H("The Square-Root-21 Pell Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sqrt-twenty-one-pell-tower-invariant"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower.sqrt_twenty_one_pell_tower_invariant"),
                H("The fundamental-unit orbit preserves the Pell equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("x"), Underscore, F.Id("n"), Caret, D(2), Minus, D(2), D(1),
                    F.Id("y"), Underscore, F.Id("n"), Caret, D(2), Eq, D(4)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Work in the rational quadratic algebra whose generator squares to 21. "
                        + "The seed (5,1) has norm 4, while the fundamental unit (5/2,1/2) "
                        + "has norm 1. If (x n,y n) is the seed multiplied by the n-th power "
                        + "of that unit, then x n squared minus 21 times y n squared is 4 "
                        + "for every natural number n. Its first x n + 1 values are 6, 24, "
                        + "and 111.")),
                    Paragraph(Text(
                        "Pinned Mathlib defines QuadraticAlgebra.norm as a MonoidHom. The Lean "
                        + "proof computes the two named norms and then applies the existing "
                        + "multiplication and power laws; it does not reprove norm "
                        + "multiplicativity.")),
                    Paragraph(Text(
                        "This closes only the norm-plus-one Pell-tower clause of remark 27.594. "
                        + "It makes no claim about the SIC reconstruction, numerical restart "
                        + "data, Zauner orbit classes, or torsion spectrum elsewhere in the "
                        + "source atom."))),
                DescribeRole.Theorem))));
}
