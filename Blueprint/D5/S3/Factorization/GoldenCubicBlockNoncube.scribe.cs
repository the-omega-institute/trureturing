using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class GoldenCubicBlockNoncubeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual Lucas cubic block is a noncube by a finite residue obstruction.",
        H("Golden Cubic Blocks Are Not Cubes"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-block-not-cube"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/GoldenCubicBlockNoncube.golden_cubic_block_not_cube"),
            H("No golden cubic block is an integer cube"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(1), Sp, Le, Sp, F.Id("j"), Sp, Rightarrow, Sp,
                new Formula.Not(Seq(
                    Exists, Sp, F.Id("t"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    new Formula.Power(F.Id("t"), D(3)), Sp, Eq, Sp,
                    Add(new Formula.Power(
                        new Formula.Subscript(F.Id("L"), new Formula.Power(D(3), F.Id("j"))),
                        D(2)), D(3))))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The cubic Lucas recurrence cycles through 4, 6, 3, 1 modulo 7. "
                + "The block therefore has residue 5 or 4 modulo 7, while integer cubes "
                + "have residue 0, 1, or 6. The obstruction applies at every positive "
                + "power-of-three index."))),
            DescribeRole.Theorem))));
}
