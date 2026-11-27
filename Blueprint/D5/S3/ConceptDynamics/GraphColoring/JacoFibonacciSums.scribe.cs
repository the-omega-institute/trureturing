using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoFibonacciSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At Fibonacci orders and sums of two Fibonacci orders the Jaco maximum degree and maximum set are given exactly by the preceding Fibonacci numbers and an explicit correction c(r,s).",
        H("Jaco graphs at Fibonacci orders and their sums"),
        Blocks(
            Node("jaco-fib-eps", "The Binet error eps_r", "eps",
                Disp(Equal(Call("eps", F.Id("r")), Subtract(new Formula.Fraction(Fib(F.Id("r")), F.Id("phi")), Fib(Subtract(F.Id("r"), D(1)))))),
                "eps r is F_r/phi-F_(r-1), with F_0=0 and F_1=1; in the proof it equals -(-1/phi)^r for r at least one. In the result, c(r,s) is 2 at r=s=4, 1 at r=s=5 and at the pairs containing an index 3 other than {3,4}, and 0 otherwise, and Iverson(P) is 1 when P holds and 0 otherwise.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-fib-result", "Maximum degrees and maximum sets at Fibonacci orders", "result", ResultFormula(),
                "Write Delta_n for the maximum degree of the finite linear Jaco graph J_n(1), J_n for its complete set of maximum-degree labels and [a,b] for the label interval. From F_(m+1)-phi F_m=psi^m, eps_r=F_r/phi-F_(r-1)=-(-1/phi)^r: eps_3=2/phi-1, eps_4=-(2-3/phi), eps_5=5/phi-3, eps_r lies in [-(5-8/phi),0) for even r at least 6 and in (0,13/phi-8] for odd r at least 7. If (n+2)/phi=(q+1)+x with x in [c(1-1/phi),(c+1)(1-1/phi)) and x<1, then JacoAdditionLaw.delta_eq_floor gives Delta_n=q, and JacoMaximumSet.result, which gives J_n=[Delta_n,R_(n-Delta_n)] with |J_n|=floor(x phi^2)+1, gives J_n=[q,q+c], because (x-c/phi^2)phi^2=x phi^2-c and 1/phi^2=1-1/phi. For n=F_r, x=2/phi+eps_r-1: for r at least 3, Delta_(F_r)=F_(r-1) and J_(F_r)=[F_(r-1),F_(r-1)+[r=3]]. For n=F_r+F_s, x=2/phi+eps_r+eps_s-1, except at r=s=4 where 2/phi+eps_4+eps_4<1 and x=2/phi+2eps_4: for r,s at least 3, Delta_(F_r+F_s)=F_(r-1)+F_(s-1)-[r=s=4] and J_(F_r+F_s)=[Delta,Delta+c] with c=2 at r=s=4, c=1 at r=s=5 and at the pairs containing an index 3 other than {3,4}, and c=0 otherwise. At the orders 6=3+3 and 10=5+5 this gives Delta_6=3, J_6={3,4,5}, Delta_10=6 and J_10={6,7}. For distinct Fibonacci orders F_r, F_s with r,s at least 4, Delta_(F_r+F_s)=Delta_(F_r)+Delta_(F_s) and J_(F_r+F_s)={Delta_(F_r)+Delta_(F_s)}. Proposition 3.2 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, pages 10-11, takes t=F_(r-1), h=F_r and l=F_s, all at least 3 (so r at least 5, s at least 4), and asserts Delta_h=F_(r-1), J_h={v_(F_(r-1))}, Delta_(h+l)=Delta_h+Delta_l and J_(h+l)={v_(Delta_h+Delta_l)}, the last two proved there through the conjectured Theorem 2.10; on that domain the first three hold and the singleton fails exactly at h=l=5. The symmetric statement for r,s at least 4, with exceptional orders (3,3) for the degree and (3,3),(5,5) for the singleton and the exceptional values above, is Corollary 10 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124. The degree formula used through JacoAdditionLaw is credited there to Patel's solution of MathDB problem 369423 and to Raso and Kok, arXiv:2611.01554v1, and the maximum-set description used through JacoMaximumSet to Patel's solution of MathDB problem 369424; the MathDB answers were not inspected. The extension to indices 3 is repo-derived.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var single = All("r", Nat(), Imp(Le(D(3), r), And(Equal(Delta(Fib(r)), Fib(Pred(r))),
            Equal(J(Fib(r)), Icc(Fib(Pred(r)), Add(Fib(Pred(r)), Bracket(Equal(r, D(3)))))))));
        var sum = Add(Fib(r), Fib(s));
        var bothFour = And(Equal(r, D(4)), Equal(s, D(4)));
        var degree = Equal(Delta(sum), Subtract(Add(Fib(Pred(r)), Fib(Pred(s))), Bracket(bothFour)));
        var set = Equal(J(sum), Icc(Delta(sum), Add(Delta(sum), Call("c", r, s))));
        var pairs = All("r", Nat(), All("s", Nat(), Imp(And(Le(D(3), r), Le(D(3), s)), And(degree, set))));
        var additive = Add(Delta(Fib(r)), Delta(Fib(s)));
        var distinct = All("r", Nat(), All("s", Nat(), Imp(And(Le(D(4), r), And(Le(D(4), s),
            new Formula.Relation(Fib(r), FormulaRelationOperator.NotEqual, Fib(s)))),
            And(Equal(Delta(sum), additive), Equal(J(sum), Set(additive))))));
        return Disp(And(single, And(pairs, distinct)));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fib(Formula n) => Call("F", n);
    private static Formula Pred(Formula n) => Subtract(n, D(1));
    private static Formula Delta(Formula n) => Call("Delta", n);
    private static Formula J(Formula n) => Call("jaconian", n);
    private static Formula Set(Formula a) => Seq(F.OpenBrace, a, F.CloseBrace);
    private static Formula Icc(Formula a, Formula b) => Call("Icc", a, b);
    private static Formula Bracket(Formula p) => Call("Iverson", p);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
