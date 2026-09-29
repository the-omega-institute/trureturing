using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class MissingRowWidthAmplifierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed surjective component with no surjective row admits Boolean tasks with "
            + "unbounded normalized-to-original width ratios.",
        H("Missing Row Width Amplifier"),
        Blocks(
            Paragraph(Text(
                "Let X, Y and Z be arbitrary finite nonempty sets and fix a surjection "
                    + "phi from X times Y onto Z. Assume that no row y maps to phi(x,y) "
                    + "is surjective. For each natural number m greater than the size "
                    + "of X let K be the cyclic group of order m, and let A and B be "
                    + "two separately labelled "
                    + "copies of the functions from Z to K. Boolean values are denoted "
                    + "by 0 and 1; the indicator below is Boolean valued.")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Paragraph(Text(
                "All products associate to the right. A tuple lists coordinates with "
                    + "their fixed labels. The singleton set has element star. The "
                    + "normalized order rho is (a,b,x,y), and the original order pi is "
                    + "(x,a,b,y). For a fixed m, the ten maps below fix exactly the "
                    + "displayed prefix and leave the displayed complementary suffix "
                    + "free. Their dependence on the same phi and m is suppressed.")),
            new DocumentBlock.DisplayFormula(RhoLayers()),
            new DocumentBlock.DisplayFormula(PiLayers()),
            Paragraph(Text(
                "For each order and each index from zero through four, P and T denote "
                    + "the prefix and suffix products in that map's displayed type. "
                    + "The range is a set of actual functions on the entire labelled "
                    + "suffix product. Equality in a range is equality of functions "
                    + "on that same product. Each width is the maximum of all five "
                    + "range cardinalities, including the initial and terminal layers.")),
            new DocumentBlock.DisplayFormula(Widths()),
            Describe.Lean(
                DescribeId.Create("missing-row-width-amplifier"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/MissingRowWidthAmplifier."
                        + "missing_row_width_amplifier"),
                H("Uniform missing-row amplification"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All displayed conclusions hold jointly. The estimates for "
                            + "the original intermediate layers and original width are "
                            + "upper bounds; they need not be attained. The quotients "
                            + "are real quotients of the natural state counts. In the "
                            + "last clause, phi, X, Y and Z stay fixed while m varies. "
                            + "Only the auxiliary alphabets vary, and every individual "
                            + "task has a finite domain and Boolean output.")),
                    Paragraph(Text(
                        "Every row image is nonempty and proper. To distinguish two "
                            + "normalized first-layer prefixes a and a prime, choose a "
                            + "coordinate z where they differ, use surjectivity to write "
                            + "z as phi(x,y), and complete with b equal to minus a. "
                            + "The first response is 1 there, and the second is 0. "
                            + "Thus the first-layer map is injective and has m to the "
                            + "power d distinct responses.")),
                    Paragraph(Text(
                        "After (a,b), the normalized response factors through the "
                            + "Boolean zero-set function on Z. After (a,b,x), it factors "
                            + "through a pair consisting of x and a Boolean function on "
                            + "its row image. In the original order, the response after "
                            + "(x,a) factors through x and the restriction of a to its "
                            + "row image; after (x,a,b), it factors through x and the "
                            + "restriction of a+b to that image. These factorizations "
                            + "retain the displayed suffix labels, including when "
                            + "different row images intersect. Counting the disjoint "
                            + "unions over x gives the stated sums as upper bounds.")),
                    Paragraph(Text(
                        "The initial prefix is a singleton. At the terminal layer, "
                            + "the suffix is a singleton and its two Boolean functions "
                            + "are attained by constant sums zero and one. Since "
                            + "m exceeds the size of X and every row has size between "
                            + "one and r, all five normalized capacities are at most "
                            + "m to the power d, and all five original capacities are "
                            + "at most the displayed sum. The exponent gap d-r is "
                            + "positive. Given R, choose a natural N greater than "
                            + "R times the size of X and take M to be the maximum "
                            + "of N and the size of X plus one. Every m at least M "
                            + "then satisfies the strict ratio inequality."))),
                DescribeRole.Theorem))));

    private static Formula Sym(string value) => F.Id(value);
    private static Formula Op(string value) => Seq(Operatorname, Grp(Sym(value)));
    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Join(Formula separator, params Formula[] values)
    {
        var items = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Tuple(params Formula[] values) => Par(Join(Comma, values));
    private static Formula Product(params Formula[] values) => Join(Times, values);
    private static Formula Apply(Formula function, params Formula[] values) =>
        Seq(function, Tuple(values));
    private static Formula Gather(params Formula[] rows) => Seq(
        Begin, Grp(Sym("gathered")), Join(RowBreak, rows), End, Grp(Sym("gathered")));
    private static Formula Set(params Formula[] values) =>
        Seq(OpenBrace, Join(Comma, values), CloseBrace);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(left, Sp, relation, Sp, right);
    private static Formula Naturals => Seq(Mathbb, Grp(Sym("N")));
    private static Formula Reals => Seq(Mathbb, Grp(Sym("R")));
    private static Formula Integers => Seq(Mathbb, Grp(Sym("Z")));
    private static Formula BoolSet => Set(D(0), D(1));
    private static Formula UnitSet => Set(Star);
    private static Formula M => Sym("m");
    private static Formula RowSize => Sub(Sym("r"), Sym("x"));
    private static Formula RowSum(Formula alphabet) => Seq(
        Sub(Sum, Rel(Sym("x"), InMacro, Sym("X"))), Sp, Pow(alphabet, RowSize));
    private static Formula Layer(Formula order, byte index) =>
        Sub(Sym("L"), Join(Comma, order, D(index)));
    private static Formula Cap(Formula order, byte index) =>
        Apply(Sub(Kappa, Join(Comma, order, D(index))), M);
    private static Formula Width(Formula order) => Apply(Sub(Sym("W"), order), M);
    private static Formula Ratio => new Formula.Fraction(Width(Rho), Width(Pi));

    private static Formula Definitions()
    {
        var x = Sym("x"); var y = Sym("y"); var a = Sym("a"); var b = Sym("b");
        var image = Sub(Sym("S"), x);
        var z = Apply(Varphi, x, y);
        var zero = Rel(Seq(Apply(a, z), Sp, Plus, Sp, Apply(b, z)), Eq, D(0));
        return Gather(
            Join(Comma, Rel(Sym("d"), Eq, Card(Sym("Z"))),
                Rel(image, Eq, Seq(OpenBrace, z, Sp, Mid, Sp,
                    y, Sp, InMacro, Sp, Sym("Y"), CloseBrace)),
                Rel(RowSize, Eq, Card(image)),
                Rel(Sym("r"), Eq, Seq(Sub(Max, Rel(x, InMacro, Sym("X"))), Sp, RowSize))),
            Join(Comma, Rel(Sym("K"), Eq, Seq(Integers, Slash, M, Sp, Integers)),
                Rel(Sym("A"), Eq, Pow(Sym("K"), Sym("Z"))),
                Rel(Sym("B"), Eq, Pow(Sym("K"), Sym("Z")))),
            Seq(Sub(Sym("F"), M), Colon, Sp,
                Product(Sym("A"), Sym("B"), Sym("X"), Sym("Y")),
                Sp, To, Sp, BoolSet),
            Rel(Apply(Sub(Sym("F"), M), a, b, x, y), Eq,
                Sub(Seq(Mathbf, Grp(D(1))), zero)));
    }

    private static Formula Map(Formula order, byte index, Formula prefix, Formula suffix,
        Formula fixedValues, Formula freeValues) => Gather(
            Seq(Layer(order, index), Colon, Sp, prefix, Sp, To, Sp,
                Par(Seq(suffix, Sp, To, Sp, BoolSet))),
            Rel(Apply(Apply(Layer(order, index), fixedValues), freeValues), Eq,
                Apply(Sub(Sym("F"), M), Sym("a"), Sym("b"), Sym("x"), Sym("y"))));

    private static Formula RhoLayers()
    {
        var a = Sym("a"); var b = Sym("b"); var x = Sym("x"); var y = Sym("y");
        var A = Sym("A"); var B = Sym("B"); var X = Sym("X"); var Y = Sym("Y");
        return Gather(
            Map(Rho, 0, UnitSet, Product(A, B, X, Y), Star, Tuple(a, b, x, y)),
            Map(Rho, 1, A, Product(B, X, Y), a, Tuple(b, x, y)),
            Map(Rho, 2, Product(A, B), Product(X, Y), Tuple(a, b), Tuple(x, y)),
            Map(Rho, 3, Product(A, B, X), Y, Tuple(a, b, x), y),
            Map(Rho, 4, Product(A, B, X, Y), UnitSet, Tuple(a, b, x, y), Star));
    }

    private static Formula PiLayers()
    {
        var a = Sym("a"); var b = Sym("b"); var x = Sym("x"); var y = Sym("y");
        var A = Sym("A"); var B = Sym("B"); var X = Sym("X"); var Y = Sym("Y");
        return Gather(
            Map(Pi, 0, UnitSet, Product(X, A, B, Y), Star, Tuple(x, a, b, y)),
            Map(Pi, 1, X, Product(A, B, Y), x, Tuple(a, b, y)),
            Map(Pi, 2, Product(X, A), Product(B, Y), Tuple(x, a), Tuple(b, y)),
            Map(Pi, 3, Product(X, A, B), Y, Tuple(x, a, b), y),
            Map(Pi, 4, Product(X, A, B, Y), UnitSet, Tuple(x, a, b, y), Star));
    }

    private static Formula Widths()
    {
        var s = SigmaLower; var i = Sym("i"); var p = Sym("p");
        var pair = Join(Comma, s, i);
        var range = Seq(OpenBrace, Apply(Sub(Sym("L"), pair), p), Sp, Mid, Sp,
            p, Sp, InMacro, Sp, Sub(Sym("P"), pair), CloseBrace);
        return Gather(
            Seq(s, Sp, InMacro, Sp, Set(Rho, Pi), Comma, Sp,
                i, Sp, InMacro, Sp, Set(D(0), D(1), D(2), D(3), D(4))),
            Seq(Sub(Sym("L"), pair), Colon, Sp, Sub(Sym("P"), pair), Sp, To, Sp,
                Par(Seq(Sub(Sym("T"), pair), Sp, To, Sp, BoolSet))),
            Rel(Apply(Sub(Kappa, pair), M), Eq, Card(range)),
            Rel(Width(Rho), Eq, Seq(Max, Sp,
                Set(Cap(Rho, 0), Cap(Rho, 1), Cap(Rho, 2), Cap(Rho, 3), Cap(Rho, 4)))),
            Rel(Width(Pi), Eq, Seq(Max, Sp,
                Set(Cap(Pi, 0), Cap(Pi, 1), Cap(Pi, 2), Cap(Pi, 3), Cap(Pi, 4)))));
    }

    private static Formula Statement()
    {
        var X = Sym("X"); var Y = Sym("Y"); var Z = Sym("Z");
        var x = Sym("x"); var y = Sym("y"); var d = Sym("d"); var r = Sym("r");
        var n = Card(X); var full = Pow(M, d); var sum = RowSum(M);
        var bound = Seq(n, Sp, Cdot, Sp, Pow(M, r));
        var rowMap = Seq(y, Sp, Mapsto, Sp, Apply(Varphi, x, y));
        var hypotheses = Join(Land, Apply(Op("Surjective"), Varphi),
            Par(Seq(Forall, Sp, x, Sp, InMacro, Sp, X, Comma, Sp,
                Neg, Sp, Apply(Op("Surjective"), Par(rowMap)))));
        var perM = Gather(
            Seq(Forall, Sp, M, Sp, InMacro, Sp, Naturals, Comma, Sp,
                n, Sp, Lt, Sp, M, Sp, Rightarrow),
            Join(Land, Rel(Cap(Rho, 0), Eq, D(1)), Rel(Cap(Pi, 0), Eq, D(1))),
            Seq(Land, Sp, Rel(Cap(Rho, 1), Eq, full)),
            Seq(Land, Sp, Rel(Cap(Rho, 2), Leq, Pow(D(2), d))),
            Seq(Land, Sp, Rel(Cap(Rho, 3), Leq, RowSum(D(2)))),
            Seq(Land, Sp, Rel(Cap(Rho, 4), Eq, D(2))),
            Seq(Land, Sp, Rel(Cap(Pi, 1), Leq, n)),
            Seq(Land, Sp, Rel(Cap(Pi, 2), Leq, sum)),
            Seq(Land, Sp, Rel(Cap(Pi, 3), Leq, sum)),
            Seq(Land, Sp, Rel(Cap(Pi, 4), Eq, D(2))),
            Seq(Land, Sp, Rel(Width(Rho), Eq, full)),
            Seq(Land, Sp, Rel(D(0), Lt, Width(Pi))),
            Seq(Land, Sp, Rel(Width(Pi), Leq, sum)),
            Seq(Land, Sp, Rel(sum, Leq, bound)),
            Seq(Land, Sp, Rel(bound, Lt, full)),
            Seq(Land, Sp, Rel(new Formula.Fraction(Pow(M, Seq(d, Minus, r)), n),
                Leq, Ratio)));
        var threshold = Sym("M"); var R = Sym("R");
        var unbounded = Gather(
            Seq(Forall, Sp, R, Sp, InMacro, Sp, Reals, Comma, Sp,
                Exists, Sp, threshold, Sp, InMacro, Sp, Naturals, Comma),
            Join(Land, Rel(n, Lt, threshold), Par(Seq(
                Forall, Sp, M, Sp, InMacro, Sp, Naturals, Comma, Sp,
                threshold, Sp, Leq, Sp, M, Sp, Rightarrow, Sp, R, Sp, Lt, Sp, Ratio))));
        return Gather(
            Seq(Forall, Sp, X, Comma, Sp, Y, Comma, Sp, Z, Comma, Sp,
                Join(Land, Apply(Op("Finite"), X), Apply(Op("Finite"), Y),
                    Apply(Op("Finite"), Z), Apply(Op("Nonempty"), X),
                    Apply(Op("Nonempty"), Y), Apply(Op("Nonempty"), Z)), Sp, Rightarrow),
            Seq(Forall, Sp, Varphi, Colon, Sp, Product(X, Y), Sp, To, Sp, Z, Comma, Sp,
                Par(hypotheses), Sp, Rightarrow),
            Par(Seq(Forall, Sp, x, Sp, InMacro, Sp, X, Comma, Sp,
                Par(Join(Land, Rel(D(1), Leq, RowSize), Rel(RowSize, Lt, d))))),
            Seq(Land, Sp, Rel(r, Lt, d)),
            Seq(Land, Sp, Par(perM)),
            Seq(Land, Sp, Par(unbounded)));
    }
}
