using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class WormholeHolonomyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/WormholeHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Round trips through observer wormholes define holonomy, with inverse bridges giving the trivial loop.",
        H("Wormhole Holonomy"),
        Blocks(
            Theorem(
                "round-trip-maps-fixed-point",
                "round_trip_maps_fixed_point",
                RoundTripMapsFixedPointFormula(),
                "Round Trip Maps Fixed Point",
                "Round trips preserve every fixed source state as a fixed state of the round-trip dynamics.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "round-trip-eq-identity-of-left-inverse",
                "round_trip_eq_identity_of_left_inverse",
                RoundTripEqIdentityOfLeftInverseFormula(),
                "Round Trip eq Identity Of Left Inverse",
                "A genuine left inverse makes the round trip equal to the identity wormhole.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-holonomy-of-left-inverse",
                "no_holonomy_of_left_inverse",
                NoHolonomyOfLeftInverseFormula(),
                "No Holonomy Of Left Inverse",
                "A left inverse rules out holonomy at every source state.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "holonomy-refutes-left-inverse",
                "holonomy_refutes_left_inverse",
                HolonomyRefutesLeftInverseFormula(),
                "Holonomy Refutes Left Inverse",
                "Any holonomy witness refutes the claim that the return bridge is a left inverse.",
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

private static Formula RoundTripMapsFixedPointFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("forward")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("backward")), Seq(F.Id("Wormhole"), Sp, F.Id("target"), Sp, F.Id("source"))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("source"), Dot, F.Id("step"), Sp, F.Id("state"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("source"), Dot, F.Id("step"), Sp, Open, Open, F.Id("roundTrip"), Sp, F.Id("forward"), Sp, F.Id("backward"), Close, Dot, F.Id("map"), Sp, F.Id("state"), Close));

private static Formula RoundTripEqIdentityOfLeftInverseFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("forward")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("backward")), Seq(F.Id("Wormhole"), Sp, F.Id("target"), Sp, F.Id("source")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("LeftInverse"), Sp, F.Id("backward"), Dot, F.Id("map"), Sp, F.Id("forward"), Dot, F.Id("map"))],
        Seq(F.Id("roundTrip"), Sp, F.Id("forward"), Sp, F.Id("backward"), Sp, Eq, Sp, F.Id("identity"), Sp, F.Id("source")));

private static Formula NoHolonomyOfLeftInverseFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("forward")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("backward")), Seq(F.Id("Wormhole"), Sp, F.Id("target"), Sp, F.Id("source"))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("LeftInverse"), Sp, F.Id("backward"), Dot, F.Id("map"), Sp, F.Id("forward"), Dot, F.Id("map"))],
        Seq(Neg, Sp, F.Id("HasHolonomyAt"), Sp, F.Id("forward"), Sp, F.Id("backward"), Sp, F.Id("state")));

private static Formula HolonomyRefutesLeftInverseFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("forward")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("backward")), Seq(F.Id("Wormhole"), Sp, F.Id("target"), Sp, F.Id("source"))), Typed(Seq(F.Id("state")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("HasHolonomyAt"), Sp, F.Id("forward"), Sp, F.Id("backward"), Sp, F.Id("state"))],
        Seq(Neg, Sp, F.Id("Function"), Dot, F.Id("LeftInverse"), Sp, F.Id("backward"), Dot, F.Id("map"), Sp, F.Id("forward"), Dot, F.Id("map")));

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
