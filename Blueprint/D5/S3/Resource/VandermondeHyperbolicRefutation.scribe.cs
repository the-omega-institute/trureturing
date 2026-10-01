using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class VandermondeHyperbolicRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Resource/VandermondeHyperbolicRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SparseCoding/barlev2026blockretrieval");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonsystematic twenty-column code over F11 refutes the universal hyperbolic tradeoff for actual whole-file iid retrieval.",
        H("A Vandermonde refutation of the universal hyperbolic bound"),
        Blocks(
            Definition("quadraticCurve", "The quadratic moment curve",
                "For a parameter x in a field, the three coordinates are 1, x and x squared. The definition is valid over any field."),
            Definition("observedTypes", "Types seen in an actual prefix",
                "For a map from physical indices to vector parameters, observedTypes is the finite set of parameters seen in the first t samples. Multiplicity remains in the physical-index sampling measure; the set records only which parameters have occurred."),
            Definition("physicalParameter", "Twenty physical sampling indices",
                "The alphabet is Fin 20. Indices zero through nine have parameter zero. Indices ten through nineteen have parameters one through ten in ZMod 11. Every physical index has probability one twentieth, independently with replacement."),
            Definition("columns", "Repeated singleton and quadratic-curve columns",
                "The column at parameter x is (1,x,x squared). There are ten copies of the first coordinate basis vector and ten other, distinct columns. Every column is nonzero because its first coordinate is one. Columns with parameters zero, one and two are independent, so the generator has rank three. The file sizes are one and two, in the original coordinate partition."),
            Definition("hyperbolicBound", "The complete all-generators assertion",
                "For a field K, positive file sizes s1,s2 with maximum at least two, k=s1+s2, any n at least k, and any rank-k indexed generator, the sum s1/E1+s2/E2 is at most one. Ei is the Bochner expectation of the actual minimum time for the uniform iid sampled-column span to contain the entire coordinate file. Systematicity, distinct columns, and the absence of zero columns are not added hypotheses."),
            Node("claim", "Bar-Lev Conjecture 1", ClaimFormula(),
                "The assertion hyperbolicBound is quantified over every FiniteFieldModel, retaining its field structure and finite carrier. This is the universal hyperbolic bound in Section V-B, Conjecture 1, of arXiv:2603.17154v2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal hyperbolic assertion is false", new Formula.Not(F.Id("claim")),
                "For the stated twenty-column code, the singleton file is recovered exactly when a zero-parameter column has been drawn or three distinct nonzero parameters have been drawn. The second file is recovered exactly when three distinct parameters have been drawn. The exact failure tails are 45(1/10)^t-80(1/20)^t+36*0^t and 10(11/20)^t+45(1/10)^t-9(1/2)^t-90(1/20)^t+45*0^t. Finite-cylinder probabilities keep all ten duplicate physical indices. Summing these tails through retrieval_time_probability_bridge gives actual expectations E1=34/19 and E2=767/171. Consequently 1/E1+2/E2=26201/26078, exceeding one by 123/26078. This admissible nonzero witness refutes the complete all-generators statement, not a systematic subcase or a projected-rank substitute.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bar-lev-2026-universal-hyperbolic-bound-refutation"), ResolutionKind.Refuted))),
        []));

    private static Formula ClaimFormula()
    {
        Formula field = F.Id("K"), firstSize = F.Id("s1"), secondSize = F.Id("s2"), length = F.Id("n"), generator = F.Id("G");
        Formula dimension = new Formula.Binary(firstSize, FormulaBinaryOperator.Add, secondSize);
        Formula sum = new Formula.Binary(new Formula.Fraction(firstSize, Call("E1", generator)),
            FormulaBinaryOperator.Add, new Formula.Fraction(secondSize, Call("E2", generator)));
        return All("K", Named("FiniteFields"), All("s1", Named("PositiveNaturals"),
            All("s2", Named("PositiveNaturals"), new Formula.Logic(
                Relation(D(2), FormulaRelationOperator.LessThanOrEqual, Call("max", firstSize, secondSize)),
                FormulaLogicOperator.Implies, All("n", Named("Naturals"), new Formula.Logic(
                    Relation(dimension, FormulaRelationOperator.LessThanOrEqual, length),
                    FormulaLogicOperator.Implies, All("G", Call("FullRankCodes", field, dimension, length),
                        Relation(sum, FormulaRelationOperator.LessThanOrEqual, D(1)))))))));
    }

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, Call(name), prose, DescribeRole.Definition, AssessedProvenance.FromRepo());

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("vandermonde-hyperbolic-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Relation(Formula left, FormulaRelationOperator operation, Formula right) => new Formula.Relation(left, operation, right);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
