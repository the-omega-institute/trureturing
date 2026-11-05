using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class RegularGraphEnergyQuadraticExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/ramanekitturmath2023regularenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjacency energy of a regular graph cannot equal 2k√2 for a positive integer k.",
        H("Regular graph adjacency energy excludes 2k√2"),
        Blocks(
            Node("claim", "Ramane–Kitturmath Conjecture 3.11", ClaimFormula(),
                "Conjecture 3.11, page 8: \"There is no regular graph with adjacency energy 2k√2, where k∈Z⁺.\" "
                    + "The source's adjacency energy is the sum of absolute values of the real adjacency eigenvalues, with multiplicities. "
                    + "The Lean encoding quantifies over every finite vertex type, its finite simple graph, a regular degree r, and every positive integer k; "
                    + "the graphEnergy and graphSpectrum definitions are the imported source definitions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is proved", ResultFormula(),
                "The characteristic polynomial has rational coefficients. Its real splitting field is normal, and an algebra automorphism sends a square root of 2 to its negative. "
                    + "The root multiset is invariant under this automorphism. A positive regular degree is a root, while the zero-sum root multiset and the positive-part estimate force the assumed energy identity to imply r ≤ 0. "
                    + "This contradicts the positive degree. The formula displays the complete proposition proved by result.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ramane-kitturmath-2023-regular-graph-energy-conjecture-3-11"),
                    ResolutionKind.Proved))),
        []));

    private static Formula ClaimFormula() => Disp(new Formula.Logic(
        F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ResultFormula() => Disp(ClaimBody());

    private static Formula ClaimBody()
    {
        Formula v = F.Id("V"), g = F.Id("G"), r = F.Id("r"), k = F.Id("k");
        Formula regular = Call("SimpleGraph.IsRegularOfDegree", g, r);
        Formula energy = Call("graphEnergy", g, F.Id("adjacency"));
        Formula target = new Formula.Binary(
            new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, Cast(k)),
            FormulaBinaryOperator.Multiply, Call("Real.sqrt", D(2)));
        Formula conclusion = new Formula.Relation(energy, FormulaRelationOperator.NotEqual, target);
        Formula positiveK = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k);
        Formula kClause = All("k", Naturals(), new Formula.Logic(positiveK,
            FormulaLogicOperator.Implies, conclusion));
        Formula rClause = All("r", Naturals(), new Formula.Logic(regular,
            FormulaLogicOperator.Implies, kClause));
        Formula instances = Instance(Call("Fintype", v),
            Instance(Call("DecidableEq", v),
                All("G", Call("SimpleGraph", v),
                    Instance(Call("DecidableRel", Call("Adj", g)), rClause))));
        return All("V", F.Id("Type"), instances);
    }

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("rke-" + selector),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(name switch {
            "Real.sqrt" => Seq(F.Id("Real"), Dot, F.Id("sqrt")),
            "SimpleGraph.IsRegularOfDegree" => Seq(F.Id("SimpleGraph"), Dot, F.Id("IsRegularOfDegree")),
            _ => F.Id(name)
        })), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(variable), Sp, Colon, Sp, type)), Comma, Sp, body);

    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
}
