using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LowFaceNeighbourBudgetsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/LowFaceNeighbourBudgets.low_face_neighbour_budgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform cosine bounds on the low-edge upper face.",
        H("Low-face neighbouring bounds"),
        Blocks(
            Paragraph(Text("The target edge occupies the first slot of the original "
                + "six-coordinate cosine, and its opposite edge occupies the fourth. "
                + "The four neighbouring positions are the second, third, fifth, and "
                + "sixth slots. A short position has value at most 5/4. Positions "
                + "remain separate even when their values or global labels coincide.")),
            Describe.Lean(
                DescribeId.Create("low-face-two-three-four-short-neighbours"),
                DeclarationHandle.Create(Declaration),
                H("Two, three, and four short positions"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At target value 2, with all five other coordinates "
                        + "in [1,2], two short neighbouring positions give cosine at "
                        + "most 70/99. Three short positions give at most "
                        + "49sqrt(6)/198. If all four are short, the bound is 17/33.")),
                    Paragraph(Text("Monotonicity raises each short neighbour to 5/4 "
                        + "and the others to 2, while lowering the opposite coordinate "
                        + "to 1. The six pair placements, four triple placements, and "
                        + "single quadruple placement then reduce to exact positive "
                        + "radicand and squared-numerator comparisons.")),
                    Paragraph(Text("These bounds hold on the entire continuous upper "
                        + "face. They do not assert that an endpoint assignment is "
                        + "simultaneously realized by identified global edges."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var y = F.Id("y");
        var z = F.Id("z");
        var o = F.Id("o");
        var v = F.Id("v");
        var w = F.Id("w");
        var h = Rat(5, 4);
        var cosine = Call("cosine", F.D(2), y, z, o, v, w);
        var box = And(new Formula[] { y, z, o, v, w }.Select(x =>
            new Formula.Relation(x, FormulaRelationOperator.MemberOf,
                Call("Icc", F.D(1), F.D(2)))).ToArray());
        var fourSmall = And(
            Le(y, h), Le(z, h), Le(v, h), Le(w, h));
        var result = And(
            Imp(Call("TwoSmall", y, z, v, w), Le(cosine, Rat(70, 99))),
            Imp(Call("ThreeSmall", y, z, v, w),
                Le(cosine, new Formula.Fraction(
                    Mul(F.D(4, 9), Call("sqrt", F.D(6))), F.D(1, 9, 8)))),
            Imp(fourSmall, Le(cosine, Rat(17, 33))));
        return All([("y", F.Id("Real")), ("z", F.Id("Real")),
            ("o", F.Id("Real")), ("v", F.Id("Real")),
            ("w", F.Id("Real"))], Imp(box, result));
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
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(left, F.Cdot, F.Sp, right);
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
