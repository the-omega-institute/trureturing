using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class EffectiveProtocolActionMonoidDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/EffectiveProtocolActionMonoid."
            + "effective_protocol_action_monoid";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Protocol words modulo equality of their state actions form a faithful effective monoid.",
        H("Effective Protocol Action Monoid"),
        Blocks(Describe.Lean(
            DescribeId.Create("protocol-action-kernel-quotient-is-faithful"),
            DeclarationHandle.Create(Declaration),
            H("The protocol action-kernel quotient is faithful"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The protocol carrier is the free monoid on the action alphabet. Two words "
                        + "are related exactly when their given action agrees on every state; "
                        + "this relation is therefore constructed from the source action rather "
                        + "than declared independently.")),
                Paragraph(Text(
                    "The public conclusion records equivalence and compatibility with "
                        + "multiplication on both sides. The effective carrier is the canonical "
                        + "quotient by the kernel of the action representation, and its action "
                        + "is induced by the canonical injective kernel lift, which proves "
                        + "faithfulness."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula action = F.Id("A");
        Formula state = F.Id("Q");
        Formula words = Call("FreeMonoid", action);
        Formula relation = F.Id("rhoAct");
        Formula first = F.Id("u");
        Formula second = F.Id("v");
        Formula point = F.Id("z");
        Formula actionEnd = Call("ActionEnd", words, state);
        Formula effective = F.Id("Mact");
        Formula induced = F.Id("alphaAct");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula relationDefinition = Seq(
            Apply(relation, first, second), Sp, Colon, Eq, Sp,
            Forall, Sp, Typed(point, state), Comma, Sp,
            Apply(first, point), Sp, Eq, Sp, Apply(second, point));
        Formula effectiveDefinition = Seq(
            effective, Sp, Colon, Eq, Sp,
            Call("ConQuotient", Call("ker", actionEnd)));
        Formula inducedDefinition = Seq(
            induced, Sp, Colon, Eq, Sp,
            Call("MulActionOfEndHom", Call("kerLift", actionEnd)));
        Formula leftCompatibility = Seq(
            Forall, Sp,
            Typed(F.Id("p"), words), Comma, Sp,
            Typed(first, words), Comma, Sp,
            Typed(second, words), Comma, Sp,
            Apply(relation, first, second), Sp, Rightarrow, Sp,
            Apply(relation,
                Seq(F.Id("p"), Sp, Cdot, Sp, first),
                Seq(F.Id("p"), Sp, Cdot, Sp, second)));
        Formula rightCompatibility = Seq(
            Forall, Sp,
            Typed(F.Id("s"), words), Comma, Sp,
            Typed(first, words), Comma, Sp,
            Typed(second, words), Comma, Sp,
            Apply(relation, first, second), Sp, Rightarrow, Sp,
            Apply(relation,
                Seq(first, Sp, Cdot, Sp, F.Id("s")),
                Seq(second, Sp, Cdot, Sp, F.Id("s"))));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, action, Comma, Sp, state, Colon, Sp, type, Comma),
            Seq(Call("MonoidAction", words, state), Comma),
            Seq(relationDefinition, Comma),
            Seq(effectiveDefinition, Comma),
            Seq(inducedDefinition, Comma),
            Seq(Call("Equivalence", relation), Sp, Land),
            Seq(Open, leftCompatibility, Close, Sp, Land),
            Seq(Open, rightCompatibility, Close, Sp, Land),
            Seq(Call("FaithfulAction", effective, state, induced), Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
