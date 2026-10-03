using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class CubicGroverTwiceOddPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/kubota2025evenperiodic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No connected 3-regular graph is 2l-periodic for an odd multiple l of 3.",
        H("Cubic Grover walks and odd periods"),
        Blocks(
            Node("grover", "Grover time evolution matrix", GroverFormula(),
                "Section 2.2 states verbatim: \"the time evolution matrix U = U(G) ∈ C^{A×A} of the Grover walk over G is defined by U_{a,b} = 2/deg_G t(b) − 1 if a = b^{−1}; 2/deg_G t(b) if t(b) = o(a) and a ≠ b^{−1}; 0 if t(b) ≠ o(a).\" The Lean conditional expression is this three-case definition, with the reversed-arc indicator inside the composability case.",
                "grover", DescribeRole.Definition),
            Node("period", "Minimum period", PeriodFormula(),
                "Section 2.2 states verbatim: \"If there exists τ ∈ N such that U^τ = I_A, then we say that the graph G is periodic and the minimum τ is period. Such a graph is also called a τ-periodic graph.\" The definition records positivity, return to the identity, and minimality among positive return times.",
                "IsPeriodOf", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubic-grover-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Question 4.11"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "After Theorem 4.10 the source asks verbatim (Question 4.11): \"Let l be an odd integer that is a multiple of 3. Do 2l-periodic 3-regular graphs exist?\" "
                    + "The encoding uses finite simple connected graphs, degree three at every vertex, and the preceding definition of period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubic-grover-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Negative answer to Question 4.11"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The integer matrix W=3U has entries 2−3 on a reversed arc and 2 on every other composable transition. Modulo 2 it is the arc-reversal permutation, whose square is the identity. The diagonal of W² is 1. If U^(2l)=I for odd l, the difference-of-powers factor Q is congruent to the identity modulo 2, so its determinant is nonzero; the adjugate identity then forces W²=9I, contradicting the diagonal. Thus U^(2l)≠I for every odd l, which answers Question 4.11."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kubota-sekido-yoshino-2023-cubic-grover-twice-odd-period"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-grover-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula AllInst(Formula v, Formula type, Formula body, params Formula[] instances) =>
        Seq(Forall, Sp, v, Colon, Sp, type, Sp, Seq(instances), Comma, Sp, body);
    private static Formula Bracket(Formula x) => Seq(OpenBracket, x, CloseBracket);
    private static Formula Eqn(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula IfThenElse(Formula c, Formula y, Formula n) =>
        Seq(F.Id("if"), Sp, c, Sp, F.Id("then"), Sp, y, Sp, F.Id("else"), Sp, n);
    private static Formula TypeV => F.Id("Type");
    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula ArcType => Dart(G);
    private static Formula GraphType => Call("SimpleGraph", V);
    private static Formula Dart(Formula g) => Seq(g, Dot, F.Id("Dart"));
    private static Formula Adj(Formula g) => Seq(g, Dot, F.Id("Adj"));
    private static Formula GroverFormula()
    {
        Formula degree = Parenthesized(Seq(Call("degree", G, Seq(B, Dot, F.Id("snd"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))));
        Formula reverse = Eqn(A, Seq(B, Dot, F.Id("symm")));
        Formula transition = Eqn(Seq(B, Dot, F.Id("snd")), Seq(A, Dot, F.Id("fst")));
        Formula composable = IfThenElse(transition,
            Seq(new Formula.Fraction(D(2), degree), Sp, Minus, Sp,
                Parenthesized(IfThenElse(reverse, D(1), D(0)))), D(0));
        Formula rhs = composable;
        Formula body = Eqn(Call("grover", G, A, B), rhs);
        return Disp(AllInst(V, TypeV, AllInst(G, GraphType, All(A, ArcType, All(B, ArcType, body)), Bracket(Call("DecidableRel", Adj(G)))), Bracket(Call("Fintype", V)), Bracket(Call("DecidableEq", V))));
    }

    private static Formula PeriodFormula()
    {
        Formula n = F.Id("n"), u = F.Id("U"), tau = Tau, sigma = SigmaLower;
        Formula matrix = Seq(Call("Matrix", n), Sp, n, Sp, Seq(Mathbb, Grp(F.Id("C"))));
        Formula minimal = All(sigma, Seq(Mathbb, Grp(F.Id("N"))), Implies(Seq(D(0), Sp, Lt, Sp, sigma),
            Implies(Seq(sigma, Sp, Lt, Sp, tau), Ne(Seq(u, Caret, sigma), D(1)))));
        Formula periodBody = And(Seq(D(0), Sp, Lt, Sp, tau),
            And(Eqn(Seq(u, Caret, tau), D(1)), Parenthesized(minimal)));
        Formula quantified = All(tau, Seq(Mathbb, Grp(F.Id("N"))), new Formula.Logic(Call("IsPeriodOf", u, tau), FormulaLogicOperator.Iff, Parenthesized(periodBody)));
        return Disp(AllInst(n, TypeV, All(u, matrix, quantified),
            Bracket(Call("Fintype", n)), Bracket(Call("DecidableEq", n))));
    }

    private static Formula ClaimFormula()
    {
        Formula l = F.Id("l"), div3 = new Formula.Relation(D(3), FormulaRelationOperator.Divides, l);
        Formula graph = Call("SimpleGraph", V);
        Formula assumptions = And(Call("Connected", G), Parenthesized(All(F.Id("v"), V,
            Eqn(Call("degree", G, F.Id("v")), D(3)))));
        Formula body = Implies(Call("Odd", l), Implies(div3,
            AllInst(V, TypeV, AllInst(G, graph, Implies(assumptions, Seq(Neg, Sp, Call("IsPeriodOf", Call("grover", G), Seq(D(2), Sp, Times, Sp, l)))), Bracket(Call("DecidableRel", Adj(G)))), Bracket(Call("Fintype", V)), Bracket(Call("DecidableEq", V)))));
        return Disp(All(l, Seq(Mathbb, Grp(F.Id("N"))), body));
    }
}
