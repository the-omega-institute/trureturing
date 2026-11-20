using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DyadicPochhammerCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient";
    private static readonly LibraryNoteRef Coefficients =
        LibraryNoteRef.Create("D5/L/Digit/kurkov2024a358612");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ascending Pochhammer coefficients of the dyadic row polynomials.",
        H("Dyadic Pochhammer coefficients"),
        Blocks(
            Node("pochhammer-basis", "pochhammerBasis", "Ascending Pochhammer basis", DescribeRole.Definition,
                "The monic ascending Pochhammer polynomials indexed by their natural degree "
                + "form the basis of the rational polynomial module."),
            Node("basis-coordinate", "coord_basis", "Coordinates of a basis polynomial", DescribeRole.Lemma,
                "The coordinate at i of the ascending Pochhammer polynomial of degree j is "
                + "one for j=i and zero otherwise."),
            Node("rational-row", "rationalRow", "Rational row polynomial", DescribeRole.Definition,
                "Map every coefficient of the integer row R(n) to the rationals."),
            Node("row-polynomial", "rowPolynomial", "Row polynomial multiplied by the variable",
                DescribeRole.Definition, "Multiply the rational row by X."),
            Node("difference", "difference", "The dyadic difference operator", DescribeRole.Definition,
                "Send P(X) to X times the difference P(X+1)−P(X), as a rational linear map."),
            Node("rational-row-odd", "rationalRow_odd", "Odd row recurrence", DescribeRole.Lemma,
                "At every index 2n+1, multiply the rational row at n by X."),
            Node("rational-row-even", "rationalRow_even", "Positive even row recurrence", DescribeRole.Lemma,
                "At index 2n with n positive, apply the dyadic difference operator to the row at n."),
            Node("difference-pochhammer", "difference_pochhammer", "Eigenvalue of a basis polynomial",
                DescribeRole.Lemma, "The degree j basis polynomial is an eigenvector of the "
                + "difference operator with eigenvalue j."),
            Node("signed-coefficient", "signedCoefficient", "Signed coordinate", DescribeRole.Definition,
                "Multiply the coordinate in column i of the row polynomial by minus one to "
                + "the power wt(n)+i, where wt is binary popcount."),
            Node("source-coordinate", "source_coordinate", "Literal A358612 correspondence", DescribeRole.Lemma,
                "For every row and column, the coordinate is the literal rational A358612 "
                + "entry times the sign with natural exponent wt(n)+2−j. Beyond the row "
                + "edge the literal array is zero. Column zero has the same zero extension."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(Coefficients),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Statement(string name)
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var x = F.Id("X");
        var p = F.Id("P");
        var twoN = Seq(D(2), Sp, Cdot, Sp, n);
        var signed = new Formula.Power(Parens(Seq(Minus, D(1))),
            Seq(Call("wt", n), Plus, i));
        return name switch
        {
            "pochhammerBasis" => Seq(Bind(j), Eqn(Call(name, j), Call("ascPochhammer", Rational, j))),
            "coord_basis" => Seq(Bind(i, j), Eqn(Call("coord", i, Call("ascPochhammer", Rational, j)),
                Call("ite", Eqn(j, i), D(1), D(0)))),
            "rationalRow" => Seq(Bind(n), Eqn(Call(name, n), Call("map", Call("R", n), Rational))),
            "rowPolynomial" => Seq(Bind(n), Eqn(Call(name, n),
                Seq(x, Sp, Cdot, Sp, Call("rationalRow", n)))),
            "difference" => Seq(Forall, Sp, p, Sp, InMacro, Sp, Seq(Rational, OpenBracket, x, CloseBracket),
                Comma, Sp, Eqn(Call(name, p), Seq(x, Sp, Cdot, Sp,
                    Parens(Seq(Call("comp", p, Seq(x, Plus, D(1))), Minus, p))))),
            "rationalRow_odd" => Seq(Bind(n), Eqn(Call("rationalRow", Seq(twoN, Plus, D(1))),
                Seq(x, Sp, Cdot, Sp, Call("rationalRow", n)))),
            "rationalRow_even" => Seq(Bind(n), D(0), Sp, Lt, Sp, n, Sp, Implies, Sp,
                Eqn(Call("rationalRow", twoN), Call("difference", Call("rationalRow", n)))),
            "difference_pochhammer" => Seq(Bind(j),
                Eqn(Call("difference", Call("ascPochhammer", Rational, j)), Seq(Cast(j, Rational),
                    Sp, Cdot, Sp, Call("ascPochhammer", Rational, j)))),
            "signedCoefficient" => Seq(Bind(n, i),
                Eqn(Call(name, n, i), Seq(signed, Sp, Cdot, Sp,
                    Call("coord", i, Call("rowPolynomial", n))))),
            "source_coordinate" => Seq(Bind(n, j), Coordinate(n, j)),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
    }

    private static Formula Coordinate(Formula n, Formula j) =>
        Eqn(Call("coord", j, Call("rowPolynomial", n)), Seq(new Formula.Power(Parens(Seq(Minus, D(1))),
            Seq(Call("wt", n), Plus, D(2), Minus, j)), Sp, Cdot, Sp, Call("T", n, j)));

    private static Formula Rational => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [.. args]);
    private static Formula Cast(Formula f, Formula type) => Parens(Seq(f, Colon, Sp, type));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Bind(params Formula[] names) => Seq(Forall, Sp,
        Seq(names.SelectMany((name, i) => i == 0 ? new[] { name } : new[] { Comma, Sp, name }).ToArray()),
        Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp);
}
