using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class WormholeCategoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/WormholeCategory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed semiconjugate bridges compose and transport fixed behavior.",
        H("Wormhole Category"),
        Blocks(
            Theorem(
                "identity-compose",
                "identity_compose",
                WormholeIdentityComposeFormula(),
                "Identity Compose",
                "Left identity for wormhole composition.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "compose-identity",
                "compose_identity",
                WormholeComposeIdentityFormula(),
                "Compose Identity",
                "Right identity for wormhole composition.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "compose-assoc",
                "compose_assoc",
                WormholeComposeAssocFormula(),
                "Compose Assoc",
                "Associativity of wormhole composition.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "maps-fixed-point",
                "maps_fixed_point",
                WormholeMapsFixedPointFormula(),
                "Maps Fixed Point",
                "A wormhole transports every fixed source state to a fixed target state.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "maps-iterate",
                "maps_iterate",
                WormholeMapsIterateFormula(),
                "Maps Iterate",
                "A wormhole transports every finite iterate of the source dynamics.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "composite-maps-fixed-point",
                "composite_maps_fixed_point",
                WormholeCompositeMapsFixedPointFormula(),
                "Composite Maps Fixed Point",
                "Composite wormholes transport fixed points across multiple worlds.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);


private static Formula WormholeIdentityComposeFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("bridge")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target")))],
        [],
        [],
        Seq(F.Id("compose"), Sp, Open, F.Id("identity"), Sp, F.Id("target"), Close, Sp, F.Id("bridge"), Sp, Eq, Sp, F.Id("bridge")));

private static Formula WormholeComposeIdentityFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("bridge")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target")))],
        [],
        [],
        Seq(F.Id("compose"), Sp, F.Id("bridge"), Sp, Open, F.Id("identity"), Sp, F.Id("source"), Close, Sp, Eq, Sp, F.Id("bridge")));

private static Formula WormholeComposeAssocFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("fourth")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("third")), Seq(F.Id("Wormhole"), Sp, F.Id("target"), Sp, F.Id("fourth"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle")))],
        [],
        [],
        Seq(F.Id("compose"), Sp, F.Id("third"), Sp, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Sp, Eq, Sp, F.Id("compose"), Sp, Open, F.Id("compose"), Sp, F.Id("third"), Sp, F.Id("second"), Close, Sp, F.Id("first")));

private static Formula WormholeMapsFixedPointFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("bridge")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("source"), Dot, F.Id("step"), Sp, F.Id("state"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("target"), Dot, F.Id("step"), Sp, Open, F.Id("bridge"), Dot, F.Id("map"), Sp, F.Id("state"), Close));

private static Formula WormholeMapsIterateFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("bridge")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("iteration")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [],
        Seq(F.Id("bridge"), Dot, F.Id("map"), Sp, Open, Open, F.Id("source"), Dot, F.Id("step"), Caret, Grp(OpenBracket, F.Id("iteration"), CloseBracket), Close, Sp, F.Id("state"), Close, Sp, Eq, Sp, Open, F.Id("target"), Dot, F.Id("step"), Caret, Grp(OpenBracket, F.Id("iteration"), CloseBracket), Close, Sp, Open, F.Id("bridge"), Dot, F.Id("map"), Sp, F.Id("state"), Close));

private static Formula WormholeCompositeMapsFixedPointFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("source"), Dot, F.Id("step"), Sp, F.Id("state"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("target"), Dot, F.Id("step"), Sp, Open, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("map"), Sp, F.Id("state"), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
