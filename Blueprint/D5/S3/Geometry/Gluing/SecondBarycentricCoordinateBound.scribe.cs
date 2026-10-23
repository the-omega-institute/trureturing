using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class SecondBarycentricCoordinateBoundDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp rank-coordinate bound in the second barycentric subdivision",
        H("The finite rank arithmetic behind the second-star coordinate estimate"),
        Blocks(
            Paragraph(Text("This document isolates the finite arithmetic in CFMP §69.3. "
                + "The second barycentric vertex is indexed by a nonempty set J of ranks in Fin(4) "
                + "containing rank 0. The rank weight of r is 1/(r+1), and rankAverage(J) is the "
                + "arithmetic mean of those weights. The complete rank set gives the sharp value 25/48. "
                + "A second statement records the corresponding parent-star linear estimate for four "
                + "coordinates whose zeroth coordinate is maximal.")),
            Describe.Lean(DescribeId.Create("rank-weight"),
                DeclarationHandle.Create(Root + "rankWeight"),
                H("Weight attached to a barycentric rank"),
                StatementSource.FromAuthor(F.Disp(RankWeightFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("NatVal(r) is the natural-number value of r. The inverse is "
                    + "taken in the real field, so the four weights are 1, 1/2, 1/3 and 1/4."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rank-average"),
                DeclarationHandle.Create(Root + "rankAverage"),
                H("Average rank weight"),
                StatementSource.FromAuthor(F.Disp(RankAverageFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum is over r in J and realCard(J) is the cardinality "
                    + "viewed in the real field. The Lean definition is total, while the theorem "
                    + "assumes rank 0 belongs to J and therefore J is nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("second-star-rank-coordinate-bound-and-sharp"),
                DeclarationHandle.Create(Root + "second_star_rank_coordinate_bound_and_sharp"),
                H("Every rank type has the 25/48 lower bound, and the full type is sharp"),
                StatementSource.FromAuthor(F.Disp(RankTheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are exactly eight subsets J of Fin(4) containing rank 0. "
                        + "The proof splits on membership of ranks 1, 2 and 3, identifies each J, "
                        + "and checks its rational average. The full set {0,1,2,3} has average "
                        + "1/4 times (1 + 1/2 + 1/3 + 1/4) = 25/48, so the bound is sharp.")),
                    Paragraph(Text("This is the finite rank-coordinate core of CFMP §69.3. It does not "
                        + "by itself identify all geometric second-star vertices, perform face gluing, "
                        + "prove the §69.4 separation statement, or construct the §69.5 ambient open "
                        + "neighborhood."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parent-star-coordinate-bound-and-sharp"),
                DeclarationHandle.Create(Root + "parent_star_coordinate_bound_and_sharp"),
                H("The corresponding parent-star linear estimate is sharp"),
                StatementSource.FromAuthor(F.Disp(ParentTheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For beta:Fin(4) to R with total sum one and beta(j) <= beta(0) "
                        + "for every j, the weighted coordinate expression "
                        + "beta(0) + beta(1)/2 + beta(2)/3 + beta(3)/4 is at least 25/48.")),
                    Paragraph(Text("Writing u_j = beta(0)-beta(j) for j=1,2,3 gives the exact identity "
                        + "25/48 + u_1/48 + 3u_2/48 + 13u_3/48. Equality occurs at "
                        + "beta(0)=beta(1)=beta(2)=beta(3)=1/4. This estimate is the coordinate "
                        + "inequality used after the literal second-star-to-parent-star reduction; "
                        + "the reduction itself is a separate theorem."))),
                DescribeRole.Theorem))));

    private static Formula RankTheoremFormula()
    {
        var bound = All("J", Finsets(FinFour()), Implies(
            In(F.D(0), Id("J")),
            Le(Call("div", Num(25), Num(48)), Call("rankAverage", Id("J")))));
        var sharp = Eq(Call("rankAverage", Call("univ", Finsets(FinFour()))), Call("div", Num(25), Num(48)));
        return And(bound, sharp);
    }

    private static Formula RankWeightFormula()
    {
        var r = Id("r");
        return All("r", FinFour(), Eq(Call("rankWeight", r),
            Call("inverse", Add(NatVal(r), Num(1)))));
    }

    private static Formula RankAverageFormula()
    {
        var j = Id("J");
        var total = Call("sum", Id("r"), j, Call("rankWeight", Id("r")));
        return All("J", Finsets(FinFour()), Eq(Call("rankAverage", j),
            Call("multiply", Call("inverse", Call("realCard", j)), total)));
    }

    private static Formula ParentTheoremFormula()
    {
        var beta = Id("beta");
        var sumOne = Eq(Call("sum", beta), F.D(1));
        var maximal = All("j", FinFour(), Le(Call("beta", Id("j")), Call("beta", F.D(0))));
        var bound = All("beta", Maps(FinFour(), Id("R")), Implies(sumOne, Implies(maximal,
            Le(Call("div", Num(25), Num(48)), ParentExpression(beta)))));
        var quarter = Call("div", Num(1), Num(4));
        var equality = Eq(Call("div", Num(25), Num(48)),
            Add(Add(Add(quarter, Call("multiply", Call("div", Num(1), Num(2)), quarter)),
                Call("multiply", Call("div", Num(1), Num(3)), quarter)),
                Call("multiply", quarter, quarter)));
        return And(bound, equality);
    }

    private static Formula ParentExpression(Formula beta) =>
        Add(Add(Add(Call("beta", F.D(0)), Call("multiply", Call("div", Num(1), Num(2)), Call("beta", F.D(1)))),
            Call("multiply", Call("div", Num(1), Num(3)), Call("beta", F.D(2)))),
            Call("multiply", Call("div", Num(1), Num(4)), Call("beta", F.D(3))));

    private static Formula FinFour() => Call("Fin", Num(4));
    private static Formula Finsets(Formula a) => Call("Finsets", a);
    private static Formula NatVal(Formula a) => Call("natValue", a);
    private static Formula Num(int value) => value switch
    {
        25 => F.D(2, 5),
        48 => F.D(4, 8),
        _ => F.D((byte)value)
    };
    private static Formula Maps(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula In(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Sp, F.Eq, F.Sp, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Sp, F.Le, F.Sp, b);
    private static Formula Implies(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Implies, F.Sp, F.Open, b, F.Close);
    private static Formula And(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Land, F.Sp, F.Open, b, F.Close);
    private static Formula Add(Formula a, Formula b) => F.Seq(a, F.Sp, F.Plus, F.Sp, b);
}
