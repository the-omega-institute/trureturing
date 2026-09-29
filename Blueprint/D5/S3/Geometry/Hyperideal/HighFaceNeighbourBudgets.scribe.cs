using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class HighFaceNeighbourBudgetsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/HighFaceNeighbourBudgets.high_face_neighbour_budgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "High-face cosine bounds for each neighbouring colour count.",
        H("High-face neighbouring bounds"),
        Blocks(
            Paragraph(Text("The target edge occupies the first of six local positions. "
                + "The second, third, fifth, and sixth positions are its four neighbours. "
                + "Each Boolean colour records whether that position is high. Equal "
                + "lengths or repeated global edges still contribute separately to the count.")),
            Describe.Lean(
                DescribeId.Create("high-face-five-neighbour-count-bounds"),
                DeclarationHandle.Create(Declaration),
                H("Five bounds indexed by the high-neighbour count"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At target value 5/4, each high neighbour lies in "
                        + "[1,5/4], each low neighbour lies in [1,2], and the opposite "
                        + "coordinate lies in [1,2]. For zero through four high "
                        + "neighbours, the respective cosine upper bounds are 31/33, "
                        + "25/sqrt(726), 81/88, 61/sqrt(4752), and 23/27.")),
                    Paragraph(Text("Coordinate monotonicity raises each neighbour to its "
                        + "colour endpoint and lowers the opposite coordinate to 1. "
                        + "All sixteen labelled colour patterns satisfy the appropriate "
                        + "positive-radicand squared comparison, including the three "
                        + "distinct placements with two high neighbours.")),
                    Paragraph(Text("The bounds hold throughout the continuous upper face. "
                        + "No endpoint realization by a face pairing is assumed."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var bY = F.Id("bY");
        var bZ = F.Id("bZ");
        var bV = F.Id("bV");
        var bW = F.Id("bW");
        var y = F.Id("y");
        var z = F.Id("z");
        var o = F.Id("o");
        var v = F.Id("v");
        var w = F.Id("w");
        var high = Rat(5, 4);
        var box = And(
            In(y, Call("Icc", F.D(1), Call("if", bY, high, F.D(2)))),
            In(z, Call("Icc", F.D(1), Call("if", bZ, high, F.D(2)))),
            In(o, Call("Icc", F.D(1), F.D(2))),
            In(v, Call("Icc", F.D(1), Call("if", bV, high, F.D(2)))),
            In(w, Call("Icc", F.D(1), Call("if", bW, high, F.D(2)))));
        return All([("bY", F.Id("Bool")), ("bZ", F.Id("Bool")),
            ("bV", F.Id("Bool")), ("bW", F.Id("Bool")),
            ("y", F.Id("Real")), ("z", F.Id("Real")),
            ("o", F.Id("Real")), ("v", F.Id("Real")),
            ("w", F.Id("Real"))],
            Imp(box, Le(Call("cosine", high, y, z, o, v, w),
                Call("q", Call("highCount", bY, bZ, bV, bW)))));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula Rat(int numerator, int denominator) =>
        new Formula.Fraction(F.D([.. numerator.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(c => (byte)(c - '0'))]),
            F.D([.. denominator.ToString(System.Globalization.CultureInfo.InvariantCulture)
                .Select(c => (byte)(c - '0'))]));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
