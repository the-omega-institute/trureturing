using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CliquePolynomial;

internal sealed class TeimooriFaalK4FreeCliqueRootsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/teimoorifaal2021sums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected graph on seven vertices contains no four-vertex clique, but its clique polynomial has a nonreal complex zero.",
        H("A K4-free graph with a nonreal clique-polynomial root"),
        Blocks(
            Describe.Lean(DescribeId.Create("tf-k4-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Teimoori Faal's Conjecture 4.1"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4.1, page 5: \"Let G be a connected K₄-free graphs, then G has only clique roots.\" Section 2, page 3, says: \"The real root of the clique polynomial of G is called the clique root of G.\" Thus every complex zero must have imaginary part zero. The vertex type V is finite, equality and adjacency are decidable, connectedness is SimpleGraph.Connected, and K₄ exclusion is SimpleGraph.CliqueFree 4. The integer polynomial is the existing D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly: its coefficient of X to the power k counts k-element vertex subsets forming a clique, with the empty clique counted once. It sums from zero through Fintype.card V; coefficients above the largest clique size vanish. Polynomial.aeval evaluates this integer polynomial in ℂ."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tf-k4-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A seven-vertex refutation"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On the vertices 0 through 6, take the undirected edges {0,3}, {0,4}, {0,5}, {0,6}, {1,3}, {1,4}, {1,5}, {1,6}, {2,3}, {2,5}, {3,4}, {3,5}, {4,6}, and {5,6}. The path [0,3,1,4,6,5,2] visits every vertex, proving connectedness. There is no four-vertex clique. The clique counts are 1, 7, 14, and 9 in sizes zero through three, followed by zeros. The clique polynomial is therefore 1+7X+14X²+9X³. Its cubic discriminant is −31. If it split over ℝ, the discriminant would be a square of a real product of root differences and hence nonnegative. Algebraic closure of ℂ then gives a complex zero outside the image of ℝ. This contradicts the assertion that all complex zeros have imaginary part zero. The theorem concerns this finite graph; it makes no assertion about a uniform family or vertex connectivity beyond connectedness."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tf2112"),
                    ResolutionKind.Refuted))), []));

    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(Qualified(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula ClaimBody()
    {
        Formula v = F.Id("V"), g = F.Id("G"), z = F.Id("z");
        Formula polynomial = Call("D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly", g);
        Formula roots = All("z", Seq(Mathbb, Grp(F.Id("C"))),
            Imp(Equal(Call("Polynomial.aeval", z, polynomial), D(0)), Equal(Call("Complex.im", z), D(0))));
        Formula body = Imp(Call("SimpleGraph.Connected", g), Imp(Call("SimpleGraph.CliqueFree", g, D(4)), roots));
        return All("V", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), Seq(
                OpenBracket, Call("DecidableRel", Qualified("G.Adj")), CloseBracket, Sp, body))));
    }
}
