using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SignedGraphSpectral;

internal sealed class MO479815Document : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/SignedGraphSpectral/MO479815.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/hameed2025signedspectraldeletion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pendant-edge counterexample to signed-graph spectral-deviation monotonicity.",
        H("MO479815 signed-graph spectral deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The source monotonicity claim"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite simple graph, every Boolean signing of unordered vertex "
                    + "pairs, and every edge, delete the edge on the same vertex carrier and "
                    + "compare the full decreasing real spectra, with multiplicity, of the signed "
                    + "and underlying adjacency matrices. The source quantity is the sum of the "
                    + "squared coordinate differences, beta_A(Sigma). The claim asserts that this "
                    + "quantity cannot increase after deletion; no connectedness, non-bridge, "
                    + "non-isolation, sign, or dimension restriction is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The monotonicity claim is refuted"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The literal universal claim is false. On Fin 4 take the paw graph with "
                        + "edges 01, 02, 12 and 03, give every edge the negative sign, and delete "
                        + "the pendant edge 03. The underlying matrices are the paw matrix and "
                        + "K3 disjoint union K1. If a, b, c are the three ordered roots of "
                        + "x^3 - x^2 - 3x + 1 in (2,3), (0,1), and (-2,-1), respectively, "
                        + "the full ordered spectra are (a,b,-1,c), (-c,1,-b,-a) before deletion "
                        + "and (2,0,-1,-1), (1,1,0,-2) after deletion. Thus beta before is "
                        + "4(1-b)^2 and beta after is 4, with a strict increase.")),
                    Paragraph(Text(
                        "The Lean proof establishes the graph and signing correspondence, both "
                        + "Hermitian matrices, characteristic polynomials, existence and ordering "
                        + "of all roots with multiplicity, and the strict beta inequality on the "
                        + "same Fin 4 carrier."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-479815-signed-spectral-deletion"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula vertices = Call("Fin", n);
        Formula graph = At(Qualified("SimpleGraph"), vertices);
        Formula signing = new Formula.TypeArrow(At(Qualified("Sym2"), vertices), F.Id("Bool"));
        Formula edge = At(Qualified("SimpleGraph", "Adj"), F.Id("G"), F.Id("u"), F.Id("v"));
        Formula deleted = At(Qualified("SimpleGraph", "deleteEdges"), F.Id("G"),
            At(Qualified("Set", "singleton"), At(Qualified("Sym2", "mk"), F.Id("u"), F.Id("v"))));
        Formula before = At(F.Id("beta"), F.Id("G"), F.Id("sigma"));
        Formula after = At(F.Id("beta"), deleted, F.Id("sigma"));
        Formula inequality = new Formula.Relation(after,
            FormulaRelationOperator.LessThanOrEqual, before);
        return All("n", Naturals(), All("G", graph, All("sigma", signing,
            All("u", vertices, All("v", vertices, Implies(edge, inequality))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        At(F.Id(name), arguments);

    private static Formula Qualified(params string[] names)
    {
        var items = new List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(name));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
