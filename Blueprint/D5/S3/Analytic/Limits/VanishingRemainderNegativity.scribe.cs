using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Limits;

internal sealed class VanishingRemainderNegativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative limit remains eventually negative after adding a vanishing remainder.",
        H("Vanishing Remainder Negativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vanishing-remainder-eventually-negative"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Limits/VanishingRemainderNegativity."
                    + "vanishing_remainder_eventually_negative"),
                H("A vanishing remainder preserves eventual negativity"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("a"), Underscore, F.Id("n"), Sp, To, Sp, Minus,
                    F.Id("c"), Comma, Sp,
                    F.Id("r"), Underscore, F.Id("n"), Sp, To, Sp, D(0), Comma, Sp,
                    F.Id("c"), Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("N"), Comma, Sp, Forall, Sp,
                    F.Id("n"), Sp, Ge, Sp, F.Id("N"), Comma, Sp,
                    F.Id("a"), Underscore, F.Id("n"), Sp, Plus, Sp,
                    F.Id("r"), Underscore, F.Id("n"), Sp, Lt, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a_n converge to -c for a strictly positive real c, and let r_n "
                        + "converge to zero. Continuity of addition makes a_n + r_n converge "
                        + "to -c, and the strict inequality -c < 0 then holds eventually.")),
                    Paragraph(Text(
                        "This closes only the asymptotic dominance clause of the source atom. "
                        + "It does not construct zeta test functions or formalize the "
                        + "decomposition of the quadratic functional into orbit, prime, and "
                        + "archimedean terms."))),
                DescribeRole.Theorem))));
}
