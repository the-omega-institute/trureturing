using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class BinaryWordFanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/BinaryWordFan.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary word traces positive unit steps in one oriented plane. Signed triangle sums give area and centered first moments, including paths of zero signed area.",
        H("The signed triangle fan of a binary word"),
        Blocks(
            Node("actual-fan", "One ordered path", "G", DescribeRole.Definition, FanFormula(),
                "True is the horizontal unit step and false is the vertical unit step. Prefix sums are the vertices of the path. Each consecutive pair contributes its determinant divided by two and that signed area times the sum of its vertices divided by three. The centered vector is the raw moment minus half the area times the endpoint. The five coordinates are the endpoint, twice the signed area, and twelve times each centered moment. No division by the total area occurs."),
            Node("online-rule", "The update using old coordinates", "U", DescribeRole.Definition, UpdateFormula(),
                "All coordinates on the right are from the same old Five value. The true branch adds the horizontal unit step; the false branch adds the vertical unit step."),
            Node("concat-rule", "The common seam correction", "star", DescribeRole.Definition, StarFormula(),
                "The seam determinant is x.u times y.v minus x.v times y.u. The area and both moment corrections use this same determinant and the signed areas of the same two paths."),
            Node("online-fan", "Appending a supplied letter", "G_append", DescribeRole.Theorem, AppendFormula(),
                "Appending a letter preserves the old vertices and adds their last triangle. The resulting arithmetic uses the old endpoint and old signed area. It is valid for the empty auxiliary word as well as every nonempty word."),
            Node("concat-fan", "Concatenating two paths", "G_concat", DescribeRole.Theorem, ConcatFormula(),
                "The five coordinates of a concatenation satisfy the signed fan concatenation formula. Both moment coordinates include the endpoint and signed-area seam terms of the same two paths."),
            Node("reverse-fan", "Reversing the complete word", "G_reverse", DescribeRole.Theorem, ReverseFormula(),
                "Reversal fixes both letter counts, negates signed area, and preserves both centered moment coordinates. This statement compares mathematical positive words in a common unit reference. It supplies no operation, acquisition, calibration, or reversal authority over a physical source.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Field(Formula x, string name) => Seq(x, Dot, F.Id(name));
    private static Formula Tuple(params Formula[] coordinates) => Call("Five", coordinates);
    private static Formula WordType() => Call("List", F.Id("Bool"));
    private static Formula Append(Formula x, Formula y) => Call("append", x, y);

    private static Formula FanFormula()
    {
        Formula w = F.Id("w"), q = Call("q", w), m = Call("m", w);
        return Disp(All("w", WordType(), Equal(Call("G", w), Tuple(
            Seq(q, Dot, D(1)), Seq(q, Dot, D(2)), Seq(D(2), Call("A", w)),
            Seq(D(1, 2), m, Dot, D(1)), Seq(D(1, 2), m, Dot, D(2))))));
    }

    private static Formula UpdateFormula()
    {
        Formula x = F.Id("x"), c = F.Id("c"), u = Field(x, "u"), v = Field(x, "v"),
            d = Field(x, "d"), e = Field(x, "e"), f = Field(x, "f");
        Formula horizontal = Tuple(Seq(u, Plus, D(1)), v, Seq(d, Minus, v),
            Seq(e, Minus, D(3), d, Minus, Multiply(u, v), Plus, v),
            Seq(f, Minus, new Formula.Power(v, D(2))));
        Formula vertical = Tuple(u, Seq(v, Plus, D(1)), Seq(d, Plus, u),
            Seq(e, Plus, new Formula.Power(u, D(2))),
            Seq(f, Minus, D(3), d, Plus, Multiply(u, v), Minus, u));
        return Disp(All("x", F.Id("Five"), All("c", F.Id("Bool"),
            Equal(Call("U", x, c), Call("if", c, horizontal, vertical)))));
    }

    private static Formula StarFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"),
            xu = Field(x, "u"), xv = Field(x, "v"), xd = Field(x, "d"),
            yu = Field(y, "u"), yv = Field(y, "v"), yd = Field(y, "d");
        Formula seam = Seq(Open, Multiply(xu, yv), Minus, Multiply(xv, yu), Close);
        return Disp(All("x", F.Id("Five"), All("y", F.Id("Five"),
            Equal(Call("star", x, y), Tuple(
                Seq(xu, Plus, yu), Seq(xv, Plus, yv), Seq(xd, Plus, yd, Plus, seam),
                Seq(Field(x, "e"), Plus, Field(y, "e"), Plus, D(3), Open,
                    Multiply(yd, xu), Minus, Multiply(xd, yu), Close, Plus, seam, Open, xu, Minus, yu, Close),
                Seq(Field(x, "f"), Plus, Field(y, "f"), Plus, D(3), Open,
                    Multiply(yd, xv), Minus, Multiply(xd, yv), Close, Plus, seam, Open, xv, Minus, yv, Close))))));
    }

    private static Formula AppendFormula()
    {
        Formula w = F.Id("w"), c = F.Id("c");
        return Disp(All("w", WordType(), All("c", F.Id("Bool"), Equal(
            Call("G", Append(w, Seq(OpenBracket, c, CloseBracket))),
            Call("U", Call("G", w), c)))));
    }

    private static Formula ConcatFormula()
    {
        Formula h = F.Id("h"), k = F.Id("k");
        return Disp(All("h", WordType(), All("k", WordType(), Equal(
            Call("G", Append(h, k)), Call("star", Call("G", h), Call("G", k))))));
    }

    private static Formula ReverseFormula()
    {
        Formula w = F.Id("w"), g = Call("G", w);
        return Disp(All("w", WordType(), Equal(Call("G", Call("reverse", w)),
            Tuple(Field(g, "u"), Field(g, "v"), Seq(Minus, Field(g, "d")),
                Field(g, "e"), Field(g, "f")))));
    }
}
