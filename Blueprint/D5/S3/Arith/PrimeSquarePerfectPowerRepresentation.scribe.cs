using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PrimeSquarePerfectPowerRepresentationDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hilliard2006a115039");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime can be added to a square to obtain a perfect power with exponent "
            + "at least two.",
        H("Prime Square Perfect-Power Representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-square-perfect-power-representation"),
                DeclarationHandle.Create(Result),
                H("Every prime has a square-to-perfect-power representation"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For the prime two, five squared plus two is three cubed. Every odd "
                        + "prime has the form two times t plus one, and t squared plus that "
                        + "prime equals (t+1) squared. Both constructions use positive bases "
                        + "and an exponent at least two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a115039-prime-square-perfect-power-representation"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Call("Prime", p), Sp, Implies, Sp,
            Exists, Sp, x, Comma, Sp, y, Comma, Sp, n, Sp, InMacro, Sp,
            Naturals(), Comma, Sp,
            D(2), Sp, Leq, Sp, n, Sp, Land, Sp,
            Pow(x, D(2)), Sp, Plus, Sp, p, Sp, Eq, Sp, Pow(y, n), Dot));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
}
