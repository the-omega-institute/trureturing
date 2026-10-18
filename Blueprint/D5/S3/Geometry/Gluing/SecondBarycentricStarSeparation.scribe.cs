using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class SecondBarycentricStarSeparationDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate separation and disjoint ambient neighborhoods for second stars",
        H("The 1/24 separation and 1/48 neighborhood core"),
        Blocks(
            Paragraph(Text("This module formalizes the arithmetic and sup-norm part of CFMP §§69.4–69.5. "
                + "The carrier is the standard coordinate simplex of Fin(4), and the coordinate-star "
                + "region at i consists of points whose i-th coordinate is at least 25/48. These regions "
                + "are the coordinate envelopes supplied by the §69.3 bound. The module proves their "
                + "1/24 separation and the disjointness of their radius-r ambient neighborhoods for "
                + "0 < r < 1/48.")),
            Describe.Lean(DescribeId.Create("standard-simplex"),
                DeclarationHandle.Create(Root + "standardSimplex"),
                H("The standard coordinate simplex"),
                StatementSource.FromAuthor(F.Disp(StandardSimplexFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinates are real functions on Fin(4). The carrier keeps "
                    + "nonnegative entries and total coordinate sum one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-star-region"),
                DeclarationHandle.Create(Root + "coordinateStarRegion"),
                H("The 25/48 coordinate envelope of a star"),
                StatementSource.FromAuthor(F.Disp(CoordinateStarRegionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the coordinate region forced by the sharp §69.3 lower "
                    + "bound. Its membership is a coordinate envelope; identifying it with the actual "
                    + "geometric closed star requires the separate second-subdivision bridge."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-star-neighborhood"),
                DeclarationHandle.Create(Root + "coordinateStarNeighborhood"),
                H("An ambient sup-norm neighborhood"),
                StatementSource.FromAuthor(F.Disp(CoordinateStarNeighborhoodFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Lean definition is a union of metric balls centered at all "
                    + "points of the coordinate-star region. The displayed existential form is the "
                    + "corresponding pointwise membership description."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-star-regions-disjoint"),
                DeclarationHandle.Create(Root + "coordinate_star_regions_disjoint"),
                H("Distinct coordinate regions are disjoint"),
                StatementSource.FromAuthor(F.Disp(DisjointFormula("coordinateStarRegion"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common point would have two distinct coordinates at least "
                    + "25/48, while all four nonnegative coordinates sum to one. Their sum would exceed "
                    + "one, giving a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-star-regions-separated"),
                DeclarationHandle.Create(Root + "coordinate_star_regions_separated"),
                H("Distinct regions have 1/24 sup-norm separation"),
                StatementSource.FromAuthor(F.Disp(SeparatedFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x in the i-region and y in the j-region, the simplex sum "
                    + "gives y_i <= 23/48. Hence x_i-y_i >= 1/24. The i-th coordinate is bounded by "
                    + "the sup norm of x-y, yielding the displayed separation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-star-neighborhood-is-open"),
                DeclarationHandle.Create(Root + "coordinate_star_neighborhood_isOpen"),
                H("Coordinate neighborhoods are open"),
                StatementSource.FromAuthor(F.Disp(OpenFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each neighborhood is a union of open metric balls, so it is open "
                    + "in the ambient function-space norm topology."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-star-region-subset-neighborhood"),
                DeclarationHandle.Create(Root + "coordinate_star_region_subset_neighborhood"),
                H("Each region lies in its neighborhood"),
                StatementSource.FromAuthor(F.Disp(SubsetFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every region point is the center of one of the balls in the union, "
                    + "so the corresponding region is contained in every positive-radius neighborhood."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-star-neighborhoods-disjoint"),
                DeclarationHandle.Create(Root + "coordinate_star_neighborhoods_disjoint"),
                H("Radius below 1/48 keeps distinct neighborhoods disjoint"),
                StatementSource.FromAuthor(F.Disp(NeighborhoodDisjointFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If an ambient point belonged to two neighborhoods, the triangle "
                    + "inequality would make the distance between their centers strictly less than 2r. "
                    + "For r<1/48 this contradicts the 1/24 separation.")),
                    Paragraph(Text("Together with the §69.3 coordinate enclosure, these statements supply "
                        + "the arithmetic core of §§69.4–69.5. They do not identify actual face-quotient "
                        + "stars with these regions, prove cross-chart compatibility, or establish a "
                        + "neighborhood in a glued manifold."))),
                DescribeRole.Theorem))));

    private static Formula StandardSimplexFormula() =>
        All("x", Maps(FinFour(), Id("R")), Iff(In(Id("x"), Call("standardSimplex")),
            And(All("i", FinFour(), Le(D(0), Call("x", Id("i")))),
                Eq(Call("sum", Id("x")), D(1)))));

    private static Formula CoordinateStarRegionFormula() =>
        All("i", FinFour(), All("x", Id("Coordinate"),
            Iff(In(Id("x"), Call("coordinateStarRegion", Id("i"))),
                And(In(Id("x"), Call("standardSimplex")),
                    Le(Call("div", Num(25), Num(48)), Call("x", Id("i")))))));

    private static Formula CoordinateStarNeighborhoodFormula() =>
        All("i", FinFour(), All("r", Id("R"), All("z", Id("Coordinate"),
            Iff(In(Id("z"), Call("coordinateStarNeighborhood", Id("i"), Id("r"))),
                Exists("x", Id("Coordinate"), And(In(Id("x"), Call("coordinateStarRegion", Id("i"))),
                    Lt(Call("norm", Subtract(Id("z"), Id("x"))), Id("r"))))))));

    private static Formula DisjointFormula(string setName) =>
        All("i", FinFour(), All("j", FinFour(), Implies(Ne(Id("i"), Id("j")),
            Call("Disjoint", Call(setName, Id("i")), Call(setName, Id("j"))))));

    private static Formula SeparatedFormula() =>
        All("i", FinFour(), All("j", FinFour(), Implies(Ne(Id("i"), Id("j")),
            All("x", Id("Coordinate"), All("y", Id("Coordinate"),
                Implies(And(In(Id("x"), Call("coordinateStarRegion", Id("i"))),
                    In(Id("y"), Call("coordinateStarRegion", Id("j")))),
                    Le(Call("div", D(1), Num(24)), Call("norm", Subtract(Id("x"), Id("y"))))))))));

    private static Formula OpenFormula() =>
        All("i", FinFour(), All("r", Id("R"), Implies(Lt(D(0), Id("r")),
            Call("IsOpen", Call("coordinateStarNeighborhood", Id("i"), Id("r"))))));

    private static Formula SubsetFormula() =>
        All("i", FinFour(), All("r", Id("R"), Implies(Lt(D(0), Id("r")),
            Call("subset", Call("coordinateStarRegion", Id("i")),
                Call("coordinateStarNeighborhood", Id("i"), Id("r"))))));

    private static Formula NeighborhoodDisjointFormula() =>
        All("i", FinFour(), All("j", FinFour(), Implies(Ne(Id("i"), Id("j")),
            All("r", Id("R"), Implies(And(Lt(D(0), Id("r")), Lt(Id("r"), Call("div", D(1), Num(48)))),
                Call("Disjoint", Call("coordinateStarNeighborhood", Id("i"), Id("r")),
                    Call("coordinateStarNeighborhood", Id("j"), Id("r"))))))));

    private static Formula FinFour() => Call("Fin", D(4));
    private static Formula Maps(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula In(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Sp, F.Eq, F.Sp, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Sp, F.Le, F.Sp, b);
    private static Formula Lt(Formula a, Formula b) => F.Seq(a, F.Sp, F.Lt, F.Sp, b);
    private static Formula Ne(Formula a, Formula b) => F.Seq(a, F.Sp, F.Neq, F.Sp, b);
    private static Formula Implies(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Implies, F.Sp, F.Open, b, F.Close);
    private static Formula Iff(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Iff, F.Sp, F.Open, b, F.Close);
    private static Formula And(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Land, F.Sp, F.Open, b, F.Close);
    private static Formula Subtract(Formula a, Formula b) => F.Seq(a, F.Sp, F.Minus, F.Sp, b);
    private static Formula D(int value) => value switch
    {
        24 => F.D(2, 4),
        25 => F.D(2, 5),
        48 => F.D(4, 8),
        _ => F.D((byte)value)
    };
    private static Formula Num(int value) => D(value);
}
