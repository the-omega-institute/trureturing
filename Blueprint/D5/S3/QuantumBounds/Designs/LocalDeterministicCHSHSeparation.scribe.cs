using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class LocalDeterministicCHSHSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/QuantumBounds/Designs/LocalDeterministicCHSHSeparation."
            + "local_deterministic_chsh_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local deterministic answer tables obey the classical bound and cannot match the fixed Bell witness.",
        H("Local Deterministic CHSH Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-deterministic-chsh-separation"),
                DeclarationHandle.Create(Declaration),
                H("Local deterministic CHSH separation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Fiber be finite and inhabited. A finite preparation consists of "
                            + "nonnegative weights summing to one, a local model supplies two "
                            + "Boolean answers on each side, and one preparation-independent "
                            + "table supplies both its window and local branches.")),
                    Paragraph(Text(
                        "Exhausting the four Boolean answers proves the pointwise absolute bound. "
                            + "The frozen finite-mixture theorem transports it through the "
                            + "preparation weights.")),
                    Paragraph(Text(
                        "The exact frozen Bell-state calculation gives two times square root two. "
                            + "The frozen shared-table theorem then excludes both a window-algebra "
                            + "character and reproduction of that Bell value by the local branch."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula fiberType = F.Id("Fiber");
        Formula preparation = F.Id("preparation");
        Formula model = F.Id("model");
        Formula table = F.Id("table");
        Formula fiber = F.Id("fiber");
        Formula two = D(2);
        Formula pointwise = new Formula.Norm(Call("chshAt", model, fiber));
        Formula mixture = new Formula.Norm(Call(
            "classicalCHSH", Call("weight", preparation), model));
        Formula bellValue = Seq(
            D(2), Sp, Cdot, Sp, Sqrt, Grp(D(2)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(fiberType, TypeUniverse()), Comma, Sp,
                OpenBracket, Call("Fintype", fiberType), CloseBracket, Comma, Sp,
                OpenBracket, Call("Nonempty", fiberType), CloseBracket, Comma),
            Seq(
                Forall, Sp,
                Typed(preparation, Call("FinitePreparation", fiberType)), Comma, Sp,
                Typed(model, Call("DeterministicFiberModel", fiberType)), Comma, Sp,
                Typed(table, Call("DeterministicAnswerTable", fiberType)), Comma),
            Seq(
                Open,
                Forall, Sp, Typed(fiber, fiberType), Comma, Sp,
                pointwise, Sp, Le, Sp, two,
                Close, Sp, Land),
            Seq(
                mixture, Sp, Le, Sp, two, Sp, Land),
            Seq(
                Call("Tr", Seq(F.Id("bellDensity"), Sp, Cdot, Sp, F.Id("chshOperator"))),
                Sp, Eq, Sp, bellValue, Sp, Land),
            Seq(
                Neg, Sp, Call("IsNoncontextual", table), Sp, Land, Sp,
                Neg, Sp, Call("ReproducesBellCHSH", preparation, table), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));
}
