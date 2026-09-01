using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenRationalShellRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero rational scales cannot collide under a positive golden shell "
            + "translation.",
        H("Golden Rational Shell Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-shell-collision-rigidity"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity.rational_shell_collision_rigidity"),
                H("Rational golden-shell collisions are trivial"),
                StatementSource.FromAuthor(RigidityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If two nonzero rational scales differ by a natural power of the orientation-preserving golden unit, then the shell depth is zero and the scales are equal.")),
                    Paragraph(Text(
                        "The proof reduces positive powers of the golden unit to a nonzero rational coefficient of the irrational golden ratio. It gives exact rigidity without a quantitative near-collision bound."))),
                DescribeRole.Theorem))));

    private static Formula RigidityFormula()
    {
        Formula q1 = new Formula.Subscript(F.Id("q"), D(1));
        Formula q2 = new Formula.Subscript(F.Id("q"), D(2));
        Formula n = F.Id("n");
        Formula shell = Seq(
            Open, F.Id("phi"), Caret, Grp(D(2)), Close, Caret, Grp(n));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, q1, Comma, Sp, q2, Colon, Sp,
            Seq(Mathbb, Grp(F.Id("Q"))), Comma, Sp, n, Colon, Sp,
            Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            q2, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            q1, Sp, Eq, Sp, shell, Sp, Cdot, Sp, q2,
            RowBreak, Grp(),
            Rightarrow, Sp, n, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            q1, Sp, Eq, Sp, q2, Dot,
            End, Grp(F.Id("gathered"))));
    }

}
