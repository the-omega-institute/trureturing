using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RowmotionIncomparableTogglesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lafreniere2025intervalclosed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interval-closed toggles at incomparable elements commute in every partially ordered set.",
        H("Commuting incomparable interval-closed toggles"), Blocks(
            Paragraph(Text("Let P be any partially ordered set. A subset S is order-convex, written OrdConnected(S), when every point between two members of S also belongs to S. The operation toggle(x,S) is the existing interval-closed toggle: form the symmetric difference of S with the singleton containing x if that set is order-convex, and otherwise leave S unchanged. This legality condition is retained at both stages of each composition.")),
            Describe.Lean(
                DescribeId.Create("rowmotion-incomparable-toggles-commute"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/RowmotionIncomparableToggles.incomparable_toggles_commute"),
                H("Commutation at incomparable points"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The incomparable-element direction of Lemma 1.8 of Lafreniere, Lewis, McNicholas, Striker and Welch, Interval-closed set rowmotion and homomesy on products of two chains, gives this commutation relation for finite partially ordered sets. The proof below also covers arbitrary partial orders and arbitrary order-convex subsets without a finiteness assumption.")),
                    Paragraph(Text("Legality of a flip at x depends only on membership at points comparable with x, provided the starting set is order-convex. To see this, compare two order-convex sets agreeing at all those points. In a proposed interval after the flip, if an endpoint or the intermediate point equals x, all memberships needed for that case lie at points comparable with x and can be transferred. If none equals x, the interval follows from the order-convexity of the starting set. Thus legality transfers in both directions.")),
                    Paragraph(Text("A toggle at y preserves order-convexity. When x and y are incomparable, it also preserves membership at every point comparable with x, so it preserves the legality of flipping x. Interchanging x and y gives the reverse statement. There are then four cases: if both flips are legal, the two singleton symmetric differences commute; if only one is legal, both compositions perform precisely that flip; and if neither is legal, both compositions retain S. The argument includes empty and infinite subsets."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Statement()
    {
        var p = F.Id("P");
        var x = F.Id("x");
        var y = F.Id("y");
        var s = F.Id("S");
        var equality = new Formula.Relation(
            Call("toggle", x, Call("toggle", y, s)), FormulaRelationOperator.Equal,
            Call("toggle", y, Call("toggle", x, s)));
        return All("P", F.Id("Type"),
            Seq(OpenBracket, Call("PartialOrder", p), CloseBracket, Comma, Sp,
                All("x", p, All("y", p, All("S", Call("Set", p),
                    Imp(And(new Formula.Not(P(LE(x, y))),
                        And(new Formula.Not(P(LE(y, x))), Call("OrdConnected", s))), equality))))));
    }
}
