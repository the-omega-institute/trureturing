using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubgroupGenerating;

internal sealed class ZagrebInequalityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/das2025sgbzagreb");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Zagreb inequality for the complete subgroup-generating graph.", H("ZagrebInequality"), Blocks(
            Describe.Lean(DescribeId.Create("zagreb-first"),
                DeclarationHandle.Create(Owner + "firstZagreb"), H("First Zagreb index"),
                StatementSource.FromAuthor(FirstFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite simple graph, the first Zagreb index is the real sum of squared degrees over every vertex. Isolated vertices stay in the carrier and contribute zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-endpoint-product"),
                DeclarationHandle.Create(Owner + "endpointProduct"), H("Unordered endpoint product"),
                StatementSource.FromAuthor(EndpointFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplication of endpoint degrees is symmetric, so it defines a real function on unordered vertex pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-second"),
                DeclarationHandle.Create(Owner + "secondZagreb"), H("Second Zagreb index"),
                StatementSource.FromAuthor(SecondFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The second Zagreb index sums the endpoint product over the actual unordered edge finset. Each edge occurs once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-hansen-vukicevic"),
                DeclarationHandle.Create(Owner + "hansen_vukicevic"), H("All finite groups"),
                StatementSource.FromAuthor(HansenFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group, the second Zagreb index divided by the edge count is at least the first Zagreb index divided by the vertex count. The graph has disjoint vertex parts consisting of all ordered pairs and all subgroups, with a pair adjacent precisely to the subgroup it generates. Repetitions and zero fibers are retained. There is no nonabelian, nontrivial or two-generator assumption.")),
                    Paragraph(Text("Write m for the square of the group order, k for the number of all subgroups, and r(H) for the number of ordered pairs generating H. The existing pair partition gives the sum of r(H) as m. The original degree identities give degree one at every pair vertex and degree r(H) at H. An injective map sends each ordered pair to its one unordered graph edge and its image is exactly the edge finset. Consequently the first index is m plus the sum of r(H) squared, and the second index is the sum of r(H) squared. The vertex count is m plus k and the edge count is m; both are positive, including for the trivial group.")),
                    Paragraph(Text("Source correspondence: Das, Erfanian and Nath, arXiv:2501.06124v1, Theorem 3.1 gives the two index formulas using Pr_H(G)=r(H)/m; Theorem 3.2 gives the edge and degree sums; Theorem 3.3 gives the equivalent criterion k times the sum of Pr_H(G) squared at least one. These are known source identities. The proof uses the literal graph and the established sum_pairCount, edge_count, degree_pair and degree_subgroup identities directly.")),
                    Paragraph(Text("Mathlib's sq_sum_le_card_mul_sum_sq states that m squared is at most k times the sum of r(H) squared. Clearing the two positive denominators yields the stated comparison, so the answer to the full existential Problem 3.10, printed page 13, is NO. The unordered-edge identities give the second index formula, and the two index formulas reduce the comparison to this square-sum inequality. This conclusion concerns the literal subgroup-generating graph."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("das-erfanian-nath-2025-sgb-zagreb-problem310"),
                    ResolutionKind.Proved)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Par(Seq(value, Colon, type));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Real(Formula value) => Typed(value, RealType());
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, body);
    private static Formula GraphArguments(Formula body) =>
        All("V", Named("Type"), All("finiteV", Call("Fintype", F.Id("V")),
            All("g", Call("SimpleGraph", F.Id("V")), body)));
    private static Formula Degree(Formula vertex) => Real(QCall("SimpleGraph", "degree", F.Id("g"), vertex));
    private static Formula Product() => new Formula.Binary(Degree(F.Id("u")),
        FormulaBinaryOperator.Multiply, Degree(F.Id("v")));

    private static Formula FirstFormula() => Disp(GraphArguments(Equal(
        Real(Call("firstZagreb", F.Id("g"))),
        QCall("Finset", "sum", Typed(Qualified("Finset", "univ"), Call("Finset", F.Id("V"))),
            LambdaOf("v", F.Id("V"), new Formula.Power(Degree(F.Id("v")), D(2)))))));

    private static Formula EndpointFormula()
    {
        Formula V = F.Id("V");
        Formula product = LambdaOf("u", V, LambdaOf("v", V, Product()));
        Formula symmetry = LambdaOf("u", V, LambdaOf("v", V,
            new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("mul"), Underscore, Grp(F.Id("comm"))))),
                [Degree(F.Id("u")), Degree(F.Id("v"))])));
        return Disp(GraphArguments(Equal(
            Typed(Call("endpointProduct", F.Id("g")), new Formula.TypeArrow(Call("Sym2", V), RealType())),
            QCall("Sym2", "lift", Seq(Langle, product, Comma, Sp, symmetry, Rangle)))));
    }

    private static Formula SecondFormula() => Disp(GraphArguments(Equal(
        Real(Call("secondZagreb", F.Id("g"))),
        QCall("Finset", "sum", QCall("SimpleGraph", "edgeFinset", F.Id("g")),
            LambdaOf("e", Call("Sym2", F.Id("V")), Call("endpointProduct", F.Id("g"), F.Id("e")))))));

    private static Formula HansenFormula()
    {
        Formula G = F.Id("G"), graph = Call("sgbGraph", F.Id("G"));
        return Disp(All("G", Named("Type"), All("groupG", Call("Group", G),
            All("finiteG", Call("Fintype", G), new Formula.Relation(
                new Formula.Fraction(Call("firstZagreb", graph), Real(QCall("Fintype", "card", Call("Vertex", G)))),
                FormulaRelationOperator.LessThanOrEqual,
                new Formula.Fraction(Call("secondZagreb", graph),
                    Real(QCall("Finset", "card", QCall("SimpleGraph", "edgeFinset", graph)))))))));
    }
}
