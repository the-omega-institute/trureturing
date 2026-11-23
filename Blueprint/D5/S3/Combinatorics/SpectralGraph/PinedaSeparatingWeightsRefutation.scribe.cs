using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class PinedaSeparatingWeightsRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/pinedamontoya2026separatingweights");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted paths obstruct each of the three universal separating-weight analogues.",
        H("Separating weights for three graph operators"),
        Blocks(
            Paragraph(Text("Separation requires a separable characteristic polynomial, nonzero coordinates in every nonzero right eigenvector, and pairwise distinct coordinates in the specified modes. The nonzero-coordinate requirement includes the zero eigenspace. Weights are real and strictly positive on actual unordered edges or ordered arcs. Each support has its own polynomial and its own degree.")),
            Definition("normalized", "Normalized Laplacian analogue", "NormalizedClaim",
                Undirected("normalizedSep"),
                "The operator is the symmetric normalized Laplacian I minus the adjacency matrix scaled on both sides by inverse square-root degrees. The eigenvectors are real. For the distinct-coordinate requirement the modes are orthogonal to the vector of square-root degrees."),
            Definition("adjacency", "Adjacency analogue", "AdjacencyClaim",
                Undirected("adjacencySep"),
                "The symmetric weighted adjacency has one variable per edge and zero entries off the support. The eigenvectors are real. The distinct-coordinate requirement applies at eigenvalues strictly below the largest eigenvalue."),
            Definition("directed", "Directed Laplacian analogue", "DirectedClaim",
                Directed(),
                "The loopless digraph contains a spanning out-arborescence. Rows receive arcs, so entry (i,j) of the adjacency reads the arc from j to i. The receiving-degree Laplacian is the diagonal row-sum matrix minus that adjacency. The eigenvectors are complex and the distinct-coordinate requirement applies at nonzero eigenvalues."),
            Definition("claim", "Question 7.5", "claim",
                new Formula.Logic(C("NormalizedClaim"), FormulaLogicOperator.Or,
                    new Formula.Logic(C("AdjacencyClaim"), FormulaLogicOperator.Or, C("DirectedClaim"))),
                "An affirmative answer to any of the three universal analogues would imply this disjunction."),
            Refutation("normalized-refuted", "The normalized Laplacian obstruction", "normalized_refuted",
                "NormalizedClaim",
                "The five-vertex path has consecutive weights a, b, c, d and row degrees a, a+b, b+c, c+d, d. Scale the coordinates of (bd, 0, −ad, 0, ac) by the square roots of these degrees. The resulting nonzero vector is an eigenvector at 1 and vanishes at vertices 1 and 3, indexed from zero."),
            Refutation("adjacency-refuted", "The adjacency obstruction", "adjacency_refuted",
                "AdjacencyClaim",
                "On the same path the weighted adjacency annihilates the nonzero vector (bd, 0, −ad, 0, ac). The zero coordinates at vertices 1 and 3 violate separation for every positive weighting."),
            Refutation("directed-refuted", "The receiving-degree Laplacian obstruction", "directed_refuted",
                "DirectedClaim",
                "The out-path on vertices 0, 1, 2 has arcs 0 to 1 and 1 to 2, of weights p and q. The receiving-degree Laplacian has rows (0,0,0), (−p,p,0), (0,−q,q). Its last coordinate vector is a right eigenvector at q and its first two coordinates vanish."),
            Refutation("result", "Refutation of the three analogues", "result", "claim",
                "On each of the indicated supports the nonvanishing implication would force the polynomial to vanish on the whole positive orthant. The real polynomial identity theorem on the product of positive intervals and the injective integer coefficient map force the original polynomial to be zero. This argument applies at every degree and uses only the nonzero-coordinate requirement."))));

    private static DocumentBlock Definition(string id, string title, string name, Formula body, string prose) =>
        Describe.Lean(DescribeId.Create("pineda-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Rel(C(name), FormulaRelationOperator.Equal, Parens(body)))),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Refutation(string id, string title, string name, string proposition, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("pineda-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(new Formula.Not(C(proposition)))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);

    private static Formula Undirected(string separation) =>
        All("n", C("Nat"), Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            All("G", Call("SimpleGraph", Call("Fin", F.Id("n"))),
                Imp(Member(F.Id("G"), "Connected"), Certificate(Member(F.Id("G"), "edgeSet"), separation)))));

    private static Formula Directed() =>
        All("n", C("Nat"), Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            All("G", Call("Digraph", Call("Fin", F.Id("n"))),
                Imp(All("i", Call("Fin", F.Id("n")),
                        new Formula.Not(App(Member(F.Id("G"), "Adj"), F.Id("i"), F.Id("i")))),
                    Imp(Call("HasSpanningOutArborescence", F.Id("G")),
                        Certificate(Call("Arc", F.Id("G")), "directedSep"))))));

    private static Formula Certificate(Formula index, string separation)
    {
        Formula p = F.Id("P"), w = F.Id("w"), degree = F.Id("d");
        Formula eval = Seq(C("MvPolynomial"), Dot, new Formula.Subscript(C("eval"), D(2)));
        Formula cast = App(Member(C("Int"), "castRingHom"), C("Real"));
        Formula ev = App(eval, Parens(cast), w, p);
        return Bind(FormulaQuantifier.Exists, "d", C("Nat"),
            Bind(FormulaQuantifier.Exists, "P", Call("MvPolynomial", index, C("Int")),
                new Formula.Logic(Rel(p, FormulaRelationOperator.NotEqual, D(0)), FormulaLogicOperator.And,
                    new Formula.Logic(App(Member(p, "IsHomogeneous"), degree), FormulaLogicOperator.And,
                        All("w", new Formula.TypeArrow(index, C("Real")),
                            Imp(Call("Positive", w), new Formula.Logic(Call(separation, F.Id("G"), w),
                                FormulaLogicOperator.Iff, Rel(ev, FormulaRelationOperator.NotEqual, D(0)))))))));
    }

    private static Formula C(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Member(Formula obj, string name) => Seq(obj, Dot, C(name));
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(C(name), args);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Rel(Formula lhs, FormulaRelationOperator relation, Formula rhs) =>
        new Formula.Relation(lhs, relation, rhs);
    private static Formula Imp(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parens(lhs), FormulaLogicOperator.Implies, Parens(rhs));
}
