using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class GuptaMiuraGridDispersionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miura");
    private const string InequalityQuote =
        "By Proposition 4.2 and Theorem 4.1, the diameter equals D(m, n) as soon as no integer 1-Lipschitz function on G_{m,n}, realisable or not, has dispersion exceeding D(m, n): max_ϕ disp(ϕ) ≤ D(m, n). (4)";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer grid Lipschitz functions satisfy Gupta's dispersion bound.",
        H("Gupta's rectangular-grid dispersion inequality"),
        Blocks(
            Paragraph(Text("Sorting the rows and then the columns preserves the value multiset and adjacent differences bounded by one. The sorted function and its remainder from the coordinate sum are increasing. FKG compares their centered absolute deviations. An integer center is no worse than a rational center, and reflection minimizes the coordinate-sum cost at its mean.")),
            Definition("IsLipschitz", "Integer functions with adjacent differences at most one", LipschitzFormula(),
                "Section 2, p. 2: “Every construction in this paper lives on the grid graph Gm,n, with vertex set {(i, j) : 1 ≤ i ≤ m, 1 ≤ j ≤ n} and each vertex joined to its horizontal and vertical neighbours;” The source cell (i,j) corresponds to (i−1,j−1) in Fin m × Fin n. An integer function on the grid is 1-Lipschitz when the absolute difference on each edge is at most one. No origami realisability hypothesis is imposed."),
            Definition("disp", "Integer median-dispersion", DispersionFormula(),
                "Section 4, p. 13: “Writing disp(ϕ) = min_{K∈Z} Σ_v |ϕ(v) − K| for the ℓ1 median-dispersion of an integer function ϕ on the grid”. The sum counts each vertex once. Int.natAbs is the natural absolute value, and sInf is taken in ℕ over a nonempty range of integer-center costs, hence gives their minimum."),
            Definition("D", "Dispersion of the coordinate sum", BoundFormula(),
                "Theorem 4.1, p. 13: “Let D(m, n) = min_{K∈Z} Σ_{i=1}^m Σ_{j=1}^n |(i + j) − K|. Then diam OFG(M_{m,n}) ≥ D(m, n) for all m, n ≥ 1.” The casts of i and j to ℤ are followed by addition of one, preserving the source's one-indexed coordinate sum. The infimum and summands are natural-valued."),
            Definition("claim", "Gupta inequality (4)", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                "Inequality (4), p. 14: “" + InequalityQuote + "” Here phi denotes the source's ϕ, the dimensions range over ℕ, and the statement also includes empty grids, whose dispersion is zero."),
            Describe.Lean(
                DescribeId.Create("gupta-miura-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The rectangular-grid dispersion bound"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every integer 1-Lipschitz function on every finite rectangular grid has median-dispersion at most D(m,n). Row and column sorting reduce the estimate to increasing functions, and the centered FKG comparison bounds their absolute deviations by those of the coordinate sum. Reflection pairs that sum around its mean. The source's Theorem 4.1 and Proposition 4.2 then give the stated origami diameter for positive rectangles; those origami reductions and the separate abstract ν-chain conjecture are outside this theorem."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gupta-2026-miura-grid-dispersion-inequality-4"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("gupta-miura-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integer() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula GridType(Formula m, Formula n) => Seq(Fin(m), Sp, Times, Sp, Fin(n));
    private static Formula Functions(Formula m, Formula n) => new Formula.TypeArrow(GridType(m, n), Integer());
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Integer()));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula NaturalAbs(Formula value) => App(Qualified("Int", "natAbs"), value);
    private static Formula InfRange(Formula body) => Call("sInf", App(Qualified("Set", "range"), LambdaOf("K", Integer(), body)));

    private static Formula LipschitzFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), phi = F.Id("phi"), u = F.Id("u"), v = F.Id("v");
        Formula graph = App(Qualified("SimpleGraph", "boxProd"), App(Qualified("SimpleGraph", "pathGraph"), m), App(Qualified("SimpleGraph", "pathGraph"), n));
        Formula adjacent = App(Seq(Parenthesized(graph), Dot, Named("Adj")), u, v);
        Formula bound = AtMost(Seq(Lvert, Sp, Sub(App(phi, u), App(phi, v)), Sp, Rvert), D(1));
        return All("m", Nat(), All("n", Nat(), All("phi", Functions(m, n),
            Equal(Call("IsLipschitz", phi), Parenthesized(All("u", GridType(m, n), All("v", GridType(m, n), Imp(adjacent, bound))))))));
    }

    private static Formula DispersionFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), phi = F.Id("phi");
        Formula cost = SumOver("v", GridType(m, n), NaturalAbs(Sub(App(phi, F.Id("v")), F.Id("K"))));
        return All("m", Nat(), All("n", Nat(), All("phi", Functions(m, n), Equal(Call("disp", phi), InfRange(cost)))));
    }

    private static Formula BoundFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula coordinate = Add(Parenthesized(Add(Cast(F.Id("i")), D(1))), Parenthesized(Add(Cast(F.Id("j")), D(1))));
        Formula cost = SumOver("i", Fin(m), SumOver("j", Fin(n), NaturalAbs(Sub(coordinate, F.Id("K")))));
        return All("m", Nat(), All("n", Nat(), Equal(Call("D", m, n), InfRange(cost))));
    }

    private static Formula ClaimBody()
    {
        Formula m = F.Id("m"), n = F.Id("n"), phi = F.Id("phi");
        return All("m", Nat(), All("n", Nat(), All("phi", Functions(m, n),
            Imp(Call("IsLipschitz", phi), AtMost(Call("disp", phi), Call("D", m, n))))));
    }
}
