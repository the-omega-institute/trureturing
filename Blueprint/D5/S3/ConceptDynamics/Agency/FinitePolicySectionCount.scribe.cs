using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class FinitePolicySectionCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-state deterministic policy sections are counted by the product of their legal-action fiber sizes.",
        H("Finite Policy Section Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-policy-sections-have-the-fiber-product-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount."
                        + "finite_policy_sections_card"),
                H("Policy sections have the product of the legal-fiber cardinalities"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The legality predicate constructs the total action space from state-action "
                            + "pairs. The counted policies are functions into that total space whose "
                            + "first coordinate is the state supplied to the function, so the public "
                            + "statement counts genuine sections of the projection.")),
                    Paragraph(Text(
                        "A section determines one legal action in every state fiber, and a dependent "
                            + "family of legal actions reconstructs the section with its projection "
                            + "equation. These maps are inverse before finite cardinality is taken.")),
                    Paragraph(Text(
                        "The equality does not require nonemptiness of the fibers: when a fiber is "
                            + "empty, both the section type and the dependent product are empty. Thus "
                            + "the deposited statement strengthens the finite-nonempty source case."))),
                DescribeRole.Theorem))));

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Q");
        Formula actionType = F.Id("A");
        Formula legal = F.Id("Legal");
        Formula pair = F.Id("z");
        Formula section = F.Id("s");
        Formula stateValue = F.Id("q");
        Formula action = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula productType = Seq(state, Sp, Times, Sp, actionType);
        Formula totalSpace = Seq(
            Left, OpenBrace, pair, Colon, Sp, productType, Sp, Mid, Sp,
            Call("Legal", Call("fst", pair), Call("snd", pair)),
            Right, CloseBrace);
        Formula sections = Seq(
            Left, OpenBrace,
            section, Colon, Sp, Arrow(state, totalSpace), Sp, Mid, Sp,
            Forall, Sp, stateValue, Colon, Sp, state, Comma, Sp,
            Call("fst", Apply(section, stateValue)), Sp, Eq, Sp, stateValue,
            Right, CloseBrace);
        Formula legalFiber = Seq(
            Left, OpenBrace,
            action, Colon, Sp, actionType, Sp, Mid, Sp,
            Call("Legal", stateValue, action),
            Right, CloseBrace);
        Formula productIndex = Seq(stateValue, Sp, InMacro, Sp, state);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, actionType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("Fintype", state), CloseBracket, Comma, Sp,
            legal, Colon, Sp,
            Arrow(state, Arrow(actionType, proposition)), Comma,
            RowBreak, Grp(),
            Call("NatCard", sections), Sp, Eq, Sp,
            Prod, Underscore, Grp(productIndex), Sp,
            Call("NatCard", legalFiber), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
