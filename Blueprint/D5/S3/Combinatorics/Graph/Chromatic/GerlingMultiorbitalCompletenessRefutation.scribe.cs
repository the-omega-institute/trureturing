using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chromatic;

internal sealed class GerlingMultiorbitalCompletenessRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/gerling2026multiorbital");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two faithful cyclic actions on six vertices share a multiorbital polynomial.",
        H("Failure of completeness for graph actions"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Owner + ".claim"),
                H("The complete-invariant assertion"), StatementSource.FromAuthor(F.Disp(Completeness())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite group G and natural numbers n and m, actions A and B "
                    + "have vertex sets Fin n and Fin m and preserve adjacency. Each input graph is finite, "
                    + "undirected and simple. The predicate Faithful means that "
                    + "the homomorphism into its vertex permutation group is injective. ActionIso requires "
                    + "a graph isomorphism that intertwines the actions of each element of G. The antecedent "
                    + "uses equality in the rational polynomial ring in x and y.")),
                    Paragraph(Text("A palette has x colors and its first y colors are proper. An edge forbids "
                    + "a shared proper color, including when its two endpoints coincide. At each group "
                    + "element, the fixed colorings descend to its cycle quotient. Taking the image of each "
                    + "unordered edge retains loops and merges parallel edges. For every subgroup, average "
                    + "the fixed-coloring counts over its elements, and sum the averages over all subgroups."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("The assertion is false"), StatementSource.FromAuthor(F.Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("On vertices 0 through 5 use edges 03, 13, 04, 14, 23, 24, 25, 34 "
                        + "for the first graph and 02, 12, 05, 15, 23, 24, 25, 34 for the second. "
                        + "The generator of the group of order two acts by swapping 0 and 1 and fixing "
                        + "the other four vertices. Both graphs are connected. Vertex 2 in the second graph "
                        + "has degree five. The degree multisets are (1,2,2,3,4,4) and (2,2,2,2,3,5), "
                        + "which rules out a graph isomorphism.")),
                    Paragraph(Text("Label the orbit of 0 and 1 by 0, and label original vertices 2 through 5 "
                        + "by 1 through 4. The quotient edge lists are 02, 03, 12, 13, 14, 23 and "
                        + "01, 04, 12, 13, 14, 23. The displayed lists contain no loops.")),
                    Paragraph(Text("Inclusion–exclusion over the bad edge events gives one term for each "
                        + "subset S of edges. Each component incident to an edge of S contributes a "
                        + "factor of y, every other component contributes a factor of x, and the sign is "
                        + "negative exactly when S has odd cardinality. This also counts the effect of a "
                        + "loop by restricting the color of its component.")),
                    Paragraph(Text("Both original graphs have polynomial P6 = x^6 − 8x^4y + 14x^3y + "
                        + "11x^2y^2 − 20x^2y − 16xy^2 + 18xy − 2y^3 + 10y^2 − 8y. "
                        + "Both cycle quotients have P5 = x^5 − 6x^3y + 8x^2y + 5xy^2 − 8xy "
                        + "− 4y^2 + 4y. The trivial subgroup contributes P6, and the full group "
                        + "contributes the common orbital polynomial (P6 + P5)/2. The common "
                        + "multiorbital polynomial is (3P6 + P5)/2. All evaluations on admissible "
                        + "palettes determine a bivariate polynomial: for each natural y the infinitely "
                        + "many x ≥ y determine its polynomial in x, and the infinitely many y determine "
                        + "each of its coefficients in x."))),
                DescribeRole.Theorem))));

    private static Formula Completeness()
    {
        var g = F.Id("G");
        var n = F.Id("n");
        var m = F.Id("m");
        var a = F.Id("A");
        var b = F.Id("B");
        var naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var equal = Equal(Call("multiorbital", a), Call("multiorbital", b));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("G"), F.Id("FiniteGroup")),
             new(FormulaIdentifier.Create("n"), naturals), new(FormulaIdentifier.Create("m"), naturals),
             new(FormulaIdentifier.Create("A"), Call("GraphAction", g, n)),
             new(FormulaIdentifier.Create("B"), Call("GraphAction", g, m))],
            Implies(Call("Faithful", a), Implies(Call("Faithful", b), Implies(equal, Call("ActionIso", a, b)))));
    }

    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
