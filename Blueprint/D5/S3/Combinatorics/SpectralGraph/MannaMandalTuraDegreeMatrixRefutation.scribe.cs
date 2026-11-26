using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class MannaMandalTuraDegreeMatrixRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026thresholdmasteridentity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The degree-matrix specialization of the master-identity criterion",
        H("The real degree matrix on connected threshold graphs"),
        Blocks(
            Node("IsThreshold", "Threshold graphs", ThresholdFormula(),
                "Section 1 of arXiv:2610.22838v1 starts from a singleton and allows isolated or dominating vertex additions. "
                + "The internal type Creation(n) encodes exactly n additions. Creation.graph realizes the last addition at label zero, shifting old labels by one. The isomorphism allows any vertex labeling. Type* permits an arbitrary universe level.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("degreeSpectrum", "Real eigenvalue multiset of the degree matrix", SpectrumFormula(),
                "The matrix is the ordinary degree diagonal over the reals. Its characteristic polynomial has one linear factor per vertex, so the root multiset carries algebraic multiplicities, including repeated degrees.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("allOnes", "The all-ones matrix", OnesFormula(),
                "Every entry is the real number one. This is the matrix J in the conjecture.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The criterion specialized to the degree matrix",
                Logic(Symbol("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                "Conjecture 13.9 (printed p. 18) puts unconditional integrality and spectral determination together on the left. "
                + "Section 2 supplies connectedness and the ordinary Laplacian. The two graphs in the determination clause may have different finite vertex types. The affine clause permits the real coefficients to depend on the graph. The matrix numeral one denotes the identity matrix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("not_degreeMatrix_master_identity_criterion", "Failure of the degree-matrix criterion",
                new Formula.Not(Parenthesized(ClaimBody())),
                "The degrees are integral, and the root multiset recovers the degree multiset. In a threshold creation sequence, a zero degree identifies an isolated last addition. "
                + "Cancel the last vertex and undo the old-degree shift after a dominating addition to recover the sequence. "
                + "This reconstruction is classical, due to Chvátal and Hammer (1977). "
                + "On the connected three-vertex path, the leaf nonedge forces beta to vanish and a center-to-leaf edge forces alpha to vanish. The center and leaf diagonal entries then force incompatible values of gamma.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("threshold-" + selector.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Symbol(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Symbol(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Symbol(owner), Dot, Symbol(name)), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);
    private static Formula ImpliesThat(Formula hypothesis, Formula body) =>
        Logic(hypothesis, FormulaLogicOperator.Implies, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula UniverseType() => Seq(F.Id("Type"), Star);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula VertexInstances(Formula vertices, Formula body) =>
        Instance(Call("Fintype", vertices), Instance(Call("DecidableEq", vertices), body));
    private static Formula AdjInstance(Formula graph, Formula body) =>
        Instance(Call("DecidableRel", Qualified("SimpleGraph", "Adj", graph)), body);
    private static Formula Iso(Formula left, Formula right) =>
        Call("Nonempty", Qualified("SimpleGraph", "Iso", left, right));
    private static Formula ConnectedThreshold(Formula graph, Formula body) =>
        ImpliesThat(Call("IsThreshold", graph),
            ImpliesThat(Qualified("SimpleGraph", "Connected", graph), body));
    private static Formula DegreeMatrix(Formula graph) => Qualified("SimpleGraph", "degMatrix", Reals(), graph);
    private static Formula ScalarMatrix(Formula scalar, Formula matrix) =>
        new Formula.Binary(scalar, FormulaBinaryOperator.Multiply, matrix);

    private static Formula ThresholdFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), n = F.Id("n"), c = F.Id("c");
        return All("V", UniverseType(), All("G", Call("SimpleGraph", v),
            Logic(Call("IsThreshold", g), FormulaLogicOperator.Iff,
                Parenthesized(Ex("n", Naturals(), Ex("c", Call("Creation", n),
                    Iso(g, Qualified("Creation", "graph", c))))))));
    }

    private static Formula SpectrumFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G");
        Formula roots = Qualified("Polynomial", "roots", Qualified("Matrix", "charpoly", DegreeMatrix(g)));
        return All("V", UniverseType(), VertexInstances(v, All("G", Call("SimpleGraph", v),
            AdjInstance(g, Eqn(Call("degreeSpectrum", g), roots)))));
    }

    private static Formula OnesFormula()
    {
        Formula v = F.Id("V"), i = F.Id("i"), j = F.Id("j");
        return All("V", UniverseType(), All("i", v, All("j", v,
            Eqn(Call("allOnes", v, i, j), Seq(D(1), Sp, Colon, Sp, Reals())))));
    }

    private static Formula ForGraph(Formula body)
    {
        Formula v = F.Id("V"), g = F.Id("G");
        return All("V", F.Id("Type"), VertexInstances(v,
            All("G", Call("SimpleGraph", v), AdjInstance(g, ConnectedThreshold(g, body)))));
    }

    private static Formula Integrality()
    {
        Formula g = F.Id("G"), x = F.Id("x"), z = F.Id("z");
        Formula member = Seq(x, Sp, InMacro, Sp, Call("degreeSpectrum", g));
        Formula cast = Parenthesized(Seq(z, Sp, Colon, Sp, Reals()));
        return ForGraph(All("x", Reals(), ImpliesThat(member, Ex("z", Integers(), Eqn(x, cast)))));
    }

    private static Formula Determination()
    {
        Formula v = F.Id("V"), w = F.Id("W"), g = F.Id("G"), h = F.Id("H");
        Formula same = Eqn(Call("degreeSpectrum", g), Call("degreeSpectrum", h));
        Formula body = ConnectedThreshold(g, ConnectedThreshold(h, ImpliesThat(same, Iso(g, h))));
        Formula graphs = All("G", Call("SimpleGraph", v), All("H", Call("SimpleGraph", w),
            AdjInstance(g, AdjInstance(h, body))));
        return All("V", F.Id("Type"), All("W", F.Id("Type"),
            VertexInstances(v, VertexInstances(w, graphs))));
    }

    private static Formula Affine()
    {
        Formula v = F.Id("V"), g = F.Id("G");
        Formula lap = Qualified("SimpleGraph", "lapMatrix", Reals(), g);
        Formula identity = Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix", v, v, Reals())));
        Formula rhs = Seq(ScalarMatrix(F.Id("alpha"), lap), Sp, Plus, Sp,
            ScalarMatrix(F.Id("beta"), Call("allOnes", v)), Sp, Plus, Sp,
            ScalarMatrix(F.Id("gamma"), identity));
        return ForGraph(Ex("alpha", Reals(), Ex("beta", Reals(), Ex("gamma", Reals(),
            Eqn(DegreeMatrix(g), rhs)))));
    }

    private static Formula ClaimBody() =>
        Logic(Parenthesized(Logic(Parenthesized(Integrality()), FormulaLogicOperator.And,
            Parenthesized(Determination()))), FormulaLogicOperator.Iff, Parenthesized(Affine()));
}
