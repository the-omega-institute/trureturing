using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class DynamicsDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A self-map descends uniquely through a quotient exactly when it preserves fibers.",
        H("Dynamics Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dynamics-descends-iff"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/DynamicsDescent.dynamics_descends_iff"),
                H("Fiber preservation characterizes quotient descent"),
                StatementSource.FromAuthor(DynamicsDescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a surjection from X onto B and let F be a self-map of X. "
                            + "There is a unique self-map of B making the quotient square "
                            + "commute if and only if F maps q-equivalent points to "
                            + "q-equivalent points.")),
                    Paragraph(Text(
                        "For existence, choose one representative of every fiber and apply F "
                            + "before projecting again. Fiber preservation makes this choice "
                            + "independent on the image of q. Surjectivity then makes right "
                            + "composition by q injective, which proves uniqueness.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle searches found no exact theorem combining "
                            + "both directions with uniqueness. The proof directly reuses "
                            + "Function.Surjective.injective_comp_right for the uniqueness "
                            + "step."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula DynamicsDescentFormula()
    {
        Formula xType = F.Id("X");
        Formula quotientType = F.Id("B");
        Formula quotientMap = F.Id("q");
        Formula update = F.Id("F");
        Formula descended = F.Id("descended");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, quotientType, Comma, Esc,
            Forall, Sp, quotientMap, Colon, Sp,
            xType, Sp, To, Sp, quotientType, Comma, Sp,
            update, Colon, Sp, xType, Sp, To, Sp, xType, Comma, Esc,
            Call("Surjective", quotientMap), Sp, Rightarrow, Sp,
            Left, Open,
            Exists, Bang, Sp, descended, Colon, Sp,
            quotientType, Sp, To, Sp, quotientType, Comma, Esc,
            quotientMap, Sp, Circ, Sp, update, Sp, Eq, Sp,
            descended, Sp, Circ, Sp, quotientMap,
            Right, Close, Sp, Iff, Sp,
            Left, Open,
            Forall, Sp, x, Comma, Sp, y, Comma, Esc,
            Apply(quotientMap, x), Sp, Eq, Sp, Apply(quotientMap, y),
            Sp, Rightarrow, Sp,
            Apply(quotientMap, Apply(update, x)), Sp, Eq, Sp,
            Apply(quotientMap, Apply(update, y)),
            Right, Close, Dot));
    }
}
