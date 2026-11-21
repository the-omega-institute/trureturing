using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoEdgeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum-degree vertex v_Delta is joined to the last vertex exactly when Delta_n=b_n, so the edge clause of Theorem 2.15 fails at order nineteen while its bound holds.",
        H("The edge from v_Delta to v_n"),
        Blocks(
            Node("jaco-edge-iff", "When v_Delta is joined to v_n", "edge_iff", EdgeFormula(),
                "Write Delta=Delta_n for the maximum degree of jaco n, R_i=jacoRight i=i+b_i and b_i=beattyOut i=floor((i+1)/phi). For every n at least one: R_Delta<=n, and the edge v_Delta v_n exists exactly when n=R_Delta, exactly when Delta_n=b_n, and exactly when the fractional part of (n+2)/phi lies below 1/phi. Proof: b_(n+1)=floor((n+2)/phi)=Delta_n+1 by JacoAdditionLaw.delta_eq_floor, and b_(n+1)<=n, so Delta<n; the edge between labels Delta<n exists exactly when n<=R_Delta. The existing Beatty threshold turns n+1<=R_Delta into b_(n+1)<=Delta, which is false, so R_Delta<=n; and it turns n<=R_Delta into b_n<=Delta, which by JacoDegreeShift.result (Delta_n is b_n or b_n-1) means Delta_n=b_n, equivalently the fractional-part threshold.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("jaco-edge-bound", "The bound of Theorem 2.15", "bound",
                Disp(All("k", Nat(), Le(P(Add(D(7), Multiply(D(3), F.Id("k")))), Add(D(4), Multiply(D(2), F.Id("k")))))),
                "For every k, the maximum degree at order n=7+3k is at most 4+2k=n-(3+k), the bound asserted in Theorem 2.15 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 9. It follows from delta_eq_floor because (9+3k)/phi<6+2k when phi>8/5.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("jaco-edge-claim", "The edge clause of Theorem 2.15", "claim",
                Disp(Iff(F.Id("claim"), All("k", Nat(), Call("Adj", P(Add(D(7), Multiply(D(3), F.Id("k")))), Add(D(7), Multiply(D(3), F.Id("k"))))))),
                "Theorem 2.15 of arXiv:1404.0484v1, printed page 9, asserts for every n=7+3k with k a natural number that the edge (v_Delta, v_n) exists in J_n(1). claim is that clause for every k, with the frozen adjacency of the infinite graph on labels.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-edge-result", "The edge clause fails at order nineteen", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Take k=4, so n=19. The existing maximum-degree formula gives Delta_19=floor(21/phi)-1=11, and R_11=18 by evaluating the recursive endpoint table. By edge_iff the edge would force 19=R_11=18, which is false. The bound part of Theorem 2.15 remains valid; only the edge clause fails.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula EdgeFormula()
    {
        var n = F.Id("n");
        var d = P(n);
        var adj = Call("Adj", d, n);
        return Disp(All("n", Nat(), Imp(Le(D(1), n), And(Le(Call("jacoRight", d), n),
            And(Iff(adj, Equal(n, Call("jacoRight", d))),
                And(Iff(adj, Equal(d, Call("beattyOut", n))),
                    Iff(adj, Lt(Call("frac", n), new Formula.Fraction(D(1), F.Id("phi"))))))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula P(Formula n) => Call("maxDegree", Call("jaco", n));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
