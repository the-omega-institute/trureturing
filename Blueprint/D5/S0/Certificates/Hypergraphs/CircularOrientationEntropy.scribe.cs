using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Hypergraphs;

internal sealed class CircularOrientationEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/pelekis2019orientationentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-edge three-uniform multihypergraph has greater entropy than the circle.",
        H("Circular hypergraphs do not maximise orientation-count entropy"),
        Blocks(
            Describe.Lean(DescribeId.Create("pel-circular-object"),
                DeclarationHandle.Create(Prefix + "circular"), H("All cyclic paths of size r"),
                StatementSource.FromAuthor(F.Disp(CircularFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 4, pp. 128–129, states: “Fix a positive integer r ≥ 3. A circular "
                    + "r-uniform hypergraph on n > r vertices is defined as follows: Begin with a "
                    + "cycle C_n on n vertices, identified with ℤ_n. A proper subset I ⊂ ℤ_n is a "
                    + "path in C_n if it induces a connected sub-graph of the graph C_n. The size "
                    + "of a path is the number of vertices in the corresponding induced sub-graph. "
                    + "We call a hypergraph circular if (up to isomorphism) its set of vertices is "
                    + "equal to ℤ_n and its edges are paths of C_n of size r. We denote by C_{n,r} "
                    + "the circular hypergraph on n vertices whose edge set consists of all paths "
                    + "of size r.” The edge at i contains the r successive vertices starting at i. "
                    + "The angle brackets denote the Fin n constructor; its bound proof follows "
                    + "from i : Fin n, which implies n>0. Finset.range r contains 0 through r−1. "
                    + "The modulo operation is on natural numbers. When n=0 there is no i."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pel-circular-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The circular maximality conjecture"),
                StatementSource.FromAuthor(F.Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 4, p. 129, states: “We conjecture that circular hypergraphs are such "
                    + "that H(X_{C_{n,r}}) ≥ H(X_H), for all H ∈ D_{n,n,r}.” Here r≥3 and n>r, "
                    + "as in the preceding definition. Every E has n labelled edges of size r; "
                    + "multiplicities and isolated vertices are allowed. The functions X and "
                    + "entropyX are those of OrientationEntropyBalance, with the real denominator "
                    + "r^n and logarithm of base two. This is the maximality conjecture, distinct "
                    + "from the asymptotic lower bound numbered Conjecture 4.1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pel-circular-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The circular maximality conjecture is false"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n=4 and r=3, take {0,1,2},{0,1,2},{0,1,3},{0,1,3}. Its counts for "
                    + "X=0,1,2,3,4 are (0,2,27,44,8); those of circular 4 3 are (0,0,24,48,9). "
                    + "Both counts sum to 81. The exact comparison "
                    + "2^2·27^27·44^44·8^8 < 24^24·48^48·9^9, together with "
                    + "H=log₂81−log₂(∏c^c)/81, proves a strict entropy advantage. "
                    + "Thus the circular member is not an entropy maximiser."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pelekis-2018-circular-orientation-entropy"),
                    ResolutionKind.Refuted)))));

    private static Formula CircularFormula()
    {
        var n = Id("n"); var r = Id("r"); var i = Id("i"); var j = Id("j");
        var vertex = F.Seq(F.Langle, new Formula.Modulo(Add(Call("val", i), j), n), F.Rangle);
        var image = QCall("Finset", "image", Lambda("j", Naturals(), vertex),
            QCall("Finset", "range", r));
        return All("n", Naturals(), All("r", Naturals(),
            Equal(Call("circular", n, r), Lambda("i", Call("Fin", n), image))));
    }

    private static Formula ClaimFormula()
    {
        var uniform = All("i", Call("Fin", Id("n")),
            Equal(QCall("Finset", "card", Call("E", Id("i"))), Id("r")));
        var edgeType = new Formula.TypeArrow(Call("Fin", Id("n")),
            Call("Finset", Call("Fin", Id("n"))));
        var proposition = All("r", Naturals(), All("n", Naturals(),
            Implies(Le(Num(3), Id("r")), Implies(Lt(Id("r"), Id("n")),
                All("E", edgeType, Implies(uniform,
                    Le(Call("entropyX", Id("r"), Id("E")),
                        Call("entropyX", Id("r"), Call("circular", Id("n"), Id("r"))))))))));
        return Equal(Id("claim"), proposition);
    }

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        F.Seq(Id("fun"), F.Sp, Parenthesized(F.Seq(Id(name), F.Sp, F.Colon, F.Sp, type)),
            F.Sp, F.Mapsto, F.Sp, body);
    private static Formula Q(string owner, string name) => F.Seq(F.Id(owner), F.Dot, F.Id(name));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Q(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
