using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class DeterministicPolicyProductCountDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/DeterministicPolicyProductCount."
            + "deterministic_policy_product_and_count";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Policy sections are canonically equivalent to dependent legal-action choices and have the corresponding product cardinality.",
        H("Deterministic Policy Product and Count"),
        Blocks(Describe.Lean(
            DescribeId.Create("deterministic-policy-sections-form-the-fiber-product-and-have-its-cardinality"),
            DeclarationHandle.Create(Declaration),
            H("Policy sections form the legal-fiber product and obey its count"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Legality constructs the total action space from state-action pairs. A policy "
                        + "is a section of its state projection, and the displayed canonical map "
                        + "takes the action coordinate in every state.")),
                Paragraph(Text(
                    "The canonical map is bijective. The existing finite section-count theorem then "
                        + "identifies the section cardinality with the product of the legal-fiber "
                        + "cardinalities."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("Q");
        Formula actionType = F.Id("A");
        Formula legal = F.Id("Legal");
        Formula pair = F.Id("z");
        Formula section = F.Id("s");
        Formula state = F.Id("q");
        Formula action = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula productType = Seq(stateType, Sp, Times, Sp, actionType);
        Formula totalSpace = Seq(
            Left, OpenBrace, pair, Colon, Sp, productType, Sp, Mid, Sp,
            Call("Legal", Call("fst", pair), Call("snd", pair)),
            Right, CloseBrace);
        Formula sections = Seq(
            Left, OpenBrace,
            section, Colon, Sp, Arrow(stateType, totalSpace), Sp, Mid, Sp,
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            Call("fst", Apply(section, state)), Sp, Eq, Sp, state,
            Right, CloseBrace);
        Formula legalFiber = Seq(
            Left, OpenBrace,
            action, Colon, Sp, actionType, Sp, Mid, Sp,
            Call("Legal", state, action),
            Right, CloseBrace);
        Formula canonicalMap = Seq(
            Lambda, Sp, section, Colon, Sp, sections, Comma, Sp,
            Lambda, Sp, state, Colon, Sp, stateType, Comma, Sp,
            Call("snd", Apply(section, state)));
        Formula productIndex = Seq(state, Sp, InMacro, Sp, stateType);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, actionType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("Fintype", stateType), CloseBracket, Comma, Sp,
            legal, Colon, Sp,
            Arrow(stateType, Arrow(actionType, proposition)), Comma,
            RowBreak, Grp(),
            Call("Bijective", canonicalMap), Sp, Land,
            RowBreak, Grp(),
            Call("NatCard", sections), Sp, Eq, Sp,
            Prod, Underscore, Grp(productIndex), Sp,
            Call("NatCard", legalFiber), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
