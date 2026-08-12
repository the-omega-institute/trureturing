using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenFiberFirstIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected and compressed floor formulas for the first golden fiber index agree.",
        H("Equivalent Floor Formulas for the First Golden Fiber Index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-two-first-index-floor-formulas-agree"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq"),
                H("The two first-index floor formulas agree"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Esc, D(1), Sp, Leq, Sp, F.Id("a"), Sp, Implies, Sp,
                    Lfloor, Sp, F.Id("a"), Varphi, Sp, Minus, Sp,
                    Varphi, Caret, Grp(D(2)), Rfloor, Sp, Plus, Sp, D(1), Sp,
                    Eq, Sp, Lfloor, Open, F.Id("a"), Sp, Minus, Sp, D(1), Close,
                    Varphi, Rfloor))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural fiber label, the floor of a times the golden "
                        + "ratio minus its square, followed by adding one, equals the floor of "
                        + "a minus one times the golden ratio.")),
                    Paragraph(Text(
                        "The proof rewrites the square of the golden ratio as the golden ratio plus "
                        + "one, converts positivity into the exact natural subtraction cast, and "
                        + "then applies the library floor-minus-one identity. The pinned library "
                        + "contains those component identities but no declaration of their assembled "
                        + "first-index equality.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the source corollary. It covers only "
                        + "the equality between its corrected and compressed first-index formulas; "
                        + "the Beatty fiber criterion, image statement, capacity statement, and the "
                        + "joint coordinate-family claim remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
