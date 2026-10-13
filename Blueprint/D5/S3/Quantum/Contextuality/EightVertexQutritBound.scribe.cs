using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class EightVertexQutritBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/EightVertexQutritBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/tamer2026quadc5");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Wagner graph and the rank-five graph of Tamer et al. have greatest real qutrit score three, independence number three, and least dimension of a real contextuality violation four.",
        H("Sharp qutrit bounds for two eight-vertex graphs"), Blocks(
            Paragraph(Text(
                "All vector spaces and inner products are real. A realization assigns a unit vector "
                    + "to each vertex and makes vectors at adjacent vertices orthogonal. Distinct "
                    + "vertices may have equal vectors, and nonadjacent vertices may be orthogonal. "
                    + "Inner.inner with scalar field ℝ is the real inner product. A natural number "
                    + "annotated as real denotes its real cast.")),
            Node("vertex", "The eight vertex labels", "Vertex", VertexFormula(),
                "Fin 8 labels the vertices by the natural numbers from zero through seven.",
                AssessedProvenance.FromRepo()),
            Node("e", "Real Euclidean space", "E", EFormula(),
                "EuclideanSpace ℝ (Fin d) is the real d-dimensional inner product space, including d=0.",
                AssessedProvenance.FromRepo()),
            Node("w", "The Wagner graph", "W", WFormula(),
                "Table VI, rank three, specifies the Wagner graph by these twelve pairs. SimpleGraph.fromRel adds the reverse pairs and excludes loops, so the displayed relation defines an undirected simple graph.",
                AssessedProvenance.FromLiterature(Source)),
            Node("g-five", "The graph of rank five", "G5", G5Formula(),
                "These are exactly the twelve pairs in row five of Table VI. SimpleGraph.fromRel again makes the relation symmetric and irreflexive. The name G5 refers to its table rank.",
                AssessedProvenance.FromLiterature(Source)),
            Node("realizes", "Unit vectors respecting exclusivity", "Realizes", RealizesFormula(),
                "Equation (13) imposes unit length at every vertex and orthogonality on every edge. It imposes no converse to edge orthogonality and no injectivity requirement on the vector assignment.",
                AssessedProvenance.FromLiterature(Source)),
            Node("overlap-squared", "The squared real overlap", "overlapSq", OverlapSqFormula(),
                "For any two vectors in the same real Euclidean space, overlapSq raises their inner product to the second power. Neither vector is required to have unit length in this definition.",
                AssessedProvenance.FromRepo()),
            Node("score", "The sum of eight overlaps", "score", ScoreFormula(),
                "For a realization and a unit state vector, this is the expectation of the sum of the eight rank-one projectors. Equations (12) and (13) maximize that expectation over states and realizations. The function itself is defined for every vector assignment and every state vector.",
                AssessedProvenance.FromLiterature(Source)),
            Node("upper-bound", "A homogeneous bound on every state", "UpperBound", UpperBoundFormula(),
                "An upper bound c applies to every realization and every state vector, with the factor ‖ψ‖² retaining homogeneity. For unit ψ the bound is c.",
                AssessedProvenance.FromRepo()),
            Node("unit-scores", "All scores attained by unit states", "UnitScores", UnitScoresFormula(),
                "This set collects all real scores obtained from a realization in dimension d and a unit state in that same space. It is the state-expectation formulation of the optimization in Eqs. (12) and (13).",
                AssessedProvenance.FromLiterature(Source)),
            Node("eta", "The dimension-restricted supremum", "eta", EtaFormula(),
                "The quantity in Eq. (13) is expressed as sSup of UnitScores. Using a supremum defines eta for every natural dimension without assuming that a maximizing realization exists. Attainment in dimension three is stated separately below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("has-violation", "A score above the independence number", "HasViolation", HasViolationFormula(),
                "A violation is an attained unit-state score strictly above SimpleGraph.indepNum, the noncontextual bound. Equation (25) asks for the minimum dimension with such a violation; its exact minimum for the two graphs is stated using IsLeast below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("settled", "The six sharp-bound conclusions", "Settled", SettledFormula(),
                "The independence number is three. Every natural dimension at most three has the homogeneous upper bound three. Three is the greatest attained unit score in dimension three, and the dimension-three supremum equals three. The dimension-four supremum is strictly larger than three. Finally, four is the least natural dimension admitting an attained violation. IsGreatest includes both attainment and an upper bound; IsLeast includes both a violation at four and exclusion of all smaller dimensions.",
                AssessedProvenance.FromRepo()),
            Node("claim", "The proposition for both graphs", "claim", ClaimFormula(),
                "Section IV calls for an independent three-dimensional upper bound for the Wagner graph. Table V(a) gives qutrit value three and minimum dimension four for both the Wagner graph and the graph of rank five, with a dagger marking those dimension conclusions as numerical. This proposition states the exact conclusions for both graphs, including attainment and the bounds in every dimension at most three.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("eight-vertex-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Qutrit value three and minimum violation dimension four"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In ℝ³, a cycle of four unit vectors with successive orthogonality "
                            + "forces one pair of opposite vectors to agree up to sign: if one "
                            + "opposite pair is linearly independent, the other pair lies in its "
                            + "one-dimensional orthogonal complement. Applying this fact to the "
                            + "squares of either graph yields, for every realization, an edge "
                            + "with endpoints i and j such that the score for every ψ is "
                            + "2‖ψ‖² + ⟨ψ,v_i⟩² + ⟨ψ,v_j⟩². Parseval replaces the sum of "
                            + "the three squared overlaps of an orthonormal basis by ‖ψ‖², and Bessel bounds "
                            + "the last two terms by ‖ψ‖². Thus every score is at most 3‖ψ‖². "
                            + "Isometric embedding into ℝ³ gives the same bound in smaller dimensions.")),
                    Paragraph(Text(
                        "With e₀,e₁,e₂ the standard orthonormal basis of ℝ³, the vertex "
                            + "assignments (e₀,e₁,e₂,e₀,e₁,e₀,e₁,e₂) for W and "
                            + "(e₂,e₀,e₀,e₀,e₁,e₁,e₁,e₂) for G5 respect every edge. "
                            + "Taking ψ=e₀ attains score three in each case. Enumerating the "
                            + "independent subsets gives independence number three; maximum "
                            + "independent sets are {0,3,5} for W and {1,2,3} for G5.")),
                    Paragraph(Text(
                        "In ℝ⁴, normalize the eight W vectors "
                            + "(20,15,0,0), (9,−12,−12,16), (12,16,9,12), (20,−15,0,0), "
                            + "(0,0,−15,20), (16,12,12,9), (−12,9,16,−12), (0,0,15,20) "
                            + "and the state (4,0,0,3). Their unit-state score is 49449/15625. "
                            + "For G5, normalize "
                            + "(19,5,−13,0), (−2,5,29,−15), (0,0,0,−1), (8,−20,4,−15), "
                            + "(2,31,1,12), (2,−5,1,0), (−5,−2,0,0), (−1,0,2,0) "
                            + "and the state (1,2,−2,1). The score is 846537181/276109725. "
                            + "Every edge has zero inner product in both assignments, and both "
                            + "scores exceed three. These realizations, together with the sharp "
                            + "qutrit bounds, establish the real minimum dimension four indicated "
                            + "in §IV and Table V(a)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tamer-et-al-2026-eight-vertex-qutrit-dimension"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("eight-vertex-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula VertexFormula() => Equal(Local("Vertex"), FinOf(D(8)));

    private static Formula EFormula() => All("d", Naturals(),
        Equal(LocalCall("E", X("d")), Space(X("d"))));

    private static Formula WFormula() => GraphFormula("W", new Formula.SetLiteral([
        Pair(D(0), D(1)), Pair(D(1), D(2)), Pair(D(2), D(3)), Pair(D(3), D(4)),
        Pair(D(4), D(5)), Pair(D(5), D(6)), Pair(D(6), D(7)), Pair(D(7), D(0)),
        Pair(D(0), D(4)), Pair(D(1), D(5)), Pair(D(2), D(6)), Pair(D(3), D(7))]));

    private static Formula G5Formula() => GraphFormula("G5", new Formula.SetLiteral([
        Pair(D(0), D(3)), Pair(D(0), D(5)), Pair(D(1), D(4)), Pair(D(1), D(5)),
        Pair(D(1), D(6)), Pair(D(2), D(5)), Pair(D(2), D(6)), Pair(D(2), D(7)),
        Pair(D(3), D(6)), Pair(D(3), D(7)), Pair(D(4), D(7)), Pair(D(5), D(7))]));

    private static Formula GraphFormula(string name, Formula edges) => Equal(Local(name),
        At(Qualified("SimpleGraph", "fromRel"),
            LambdaOf("i", Local("Vertex"), LambdaOf("j", Local("Vertex"),
                Member(Pair(X("i"), X("j")), Typed(edges,
                    At(Qualified("Finset"), At(Qualified("Prod"), Local("Vertex"), Local("Vertex")))))))));

    private static Formula RealizesFormula()
    {
        Formula normalized = All("i", Local("Vertex"), Equal(Norm(At(X("v"), X("i"))), D(1)));
        Formula orthogonal = All("i", Local("Vertex"), All("j", Local("Vertex"),
            Implication(Adjacent(X("G"), X("i"), X("j")),
                Equal(Inner(At(X("v"), X("i")), At(X("v"), X("j"))), D(0)))));
        return All("d", Naturals(), All("G", GraphType(), All("v", Assignment(X("d")),
            Equivalence(LocalCall("Realizes", X("G"), X("v")), And(normalized, orthogonal)))));
    }

    private static Formula OverlapSqFormula() => All("d", Naturals(),
        All("psi", Space(X("d")), All("x", Space(X("d")),
            Equal(LocalCall("overlapSq", X("psi"), X("x")), Square(Inner(X("psi"), X("x")))))));

    private static Formula ScoreFormula() => All("d", Naturals(), All("v", Assignment(X("d")),
        All("psi", Space(X("d")), Equal(LocalCall("score", X("v"), X("psi")),
            SumOver("i", Local("Vertex"), LocalCall("overlapSq", X("psi"), At(X("v"), X("i"))))))));

    private static Formula UpperBoundFormula() => All("G", GraphType(), All("d", Naturals(),
        All("c", Reals(), Equivalence(LocalCall("UpperBound", X("G"), X("d"), X("c")),
            All("v", Assignment(X("d")), Implication(LocalCall("Realizes", X("G"), X("v")),
                All("psi", Space(X("d")), LE(LocalCall("score", X("v"), X("psi")),
                    Multiply(X("c"), Square(Norm(X("psi"))))))))))));

    private static Formula UnitScoresFormula() => All("G", GraphType(), All("d", Naturals(),
        Equal(LocalCall("UnitScores", X("G"), X("d")), SetOf("t", Reals(),
            Ex("v", Assignment(X("d")), And(LocalCall("Realizes", X("G"), X("v")),
                Ex("psi", Space(X("d")), And(Equal(Norm(X("psi")), D(1)),
                    Equal(LocalCall("score", X("v"), X("psi")), X("t"))))))))));

    private static Formula EtaFormula() => All("G", GraphType(), All("d", Naturals(),
        Equal(LocalCall("eta", X("G"), X("d")),
            At(Qualified("sSup"), LocalCall("UnitScores", X("G"), X("d"))))));

    private static Formula HasViolationFormula() => All("G", GraphType(), All("d", Naturals(),
        Equivalence(LocalCall("HasViolation", X("G"), X("d")),
            Ex("v", Assignment(X("d")), And(LocalCall("Realizes", X("G"), X("v")),
                Ex("psi", Space(X("d")), And(Equal(Norm(X("psi")), D(1)),
                    Less(Typed(IndependenceNumber(X("G")), Reals()),
                        LocalCall("score", X("v"), X("psi"))))))))));

    private static Formula SettledFormula()
    {
        Formula independence = Equal(IndependenceNumber(X("G")), D(3));
        Formula lowerDimensions = All("d", Naturals(), Implication(LE(X("d"), D(3)),
            LocalCall("UpperBound", X("G"), X("d"), D(3))));
        Formula greatest = At(Qualified("IsGreatest"), LocalCall("UnitScores", X("G"), D(3)), D(3));
        Formula qutritValue = Equal(LocalCall("eta", X("G"), D(3)), D(3));
        Formula fourValue = Less(D(3), LocalCall("eta", X("G"), D(4)));
        Formula leastDimension = At(Qualified("IsLeast"),
            SetOf("d", Naturals(), LocalCall("HasViolation", X("G"), X("d"))), D(4));
        return All("G", GraphType(), Equivalence(LocalCall("Settled", X("G")),
            And(independence, And(lowerDimensions, And(greatest,
                And(qutritValue, And(fourValue, leastDimension)))))));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"),
        And(LocalCall("Settled", Local("W")), LocalCall("Settled", Local("G5"))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Contextuality", "EightVertexQutritBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Space(Formula d) => At(Qualified("EuclideanSpace"), Reals(), FinOf(d));
    private static Formula GraphType() => At(Qualified("SimpleGraph"), Local("Vertex"));
    private static Formula Assignment(Formula d) => Parenthesized(new Formula.TypeArrow(Local("Vertex"), Space(d)));
    private static Formula Adjacent(Formula graph, Formula i, Formula j) => At(Qualified("SimpleGraph", "Adj"), graph, i, j);
    private static Formula IndependenceNumber(Formula graph) => At(Qualified("SimpleGraph", "indepNum"), graph);
    private static Formula Inner(Formula left, Formula right) => At(Qualified("Inner", "inner"), Reals(), left, right);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
