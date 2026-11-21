using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoFibonacciSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoFibonacciSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At Fibonacci orders and sums of two Fibonacci orders the Jaco maximum degree is the sum of the preceding Fibonacci numbers, with exact exceptions for the degree and for the unique maximizer.",
        H("Jaco graphs at Fibonacci orders and their sums"),
        Blocks(
            Node("jaco-fib-eps", "The Binet error eps_r", "eps",
                Disp(Equal(Call("eps", F.Id("r")), Subtract(new Formula.Fraction(Fib(F.Id("r")), F.Id("phi")), Fib(Subtract(F.Id("r"), D(1)))))),
                "eps r is F_r/phi-F_(r-1), with F_0=0 and F_1=1; in the proof it equals -(-1/phi)^r for r at least one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-fib-result", "Maximum degrees and maximum sets at Fibonacci orders", "result", ResultFormula(),
                "Write Delta_n for the maximum degree of the finite linear Jaco graph J_n(1) and J_n for its complete set of maximum-degree labels. From F_(m+1)-phi F_m=psi^m, eps_r=F_r/phi-F_(r-1)=-(-1/phi)^r: eps_3=2/phi-1, eps_4=-(2-3/phi), eps_5=5/phi-3, eps_r lies in [-(5-8/phi),0) for even r at least 6 and in (0,13/phi-8] for odd r at least 7. If (n+2)/phi=p+2/phi+E with 0<=2/phi+E<2, then JacoAdditionLaw.delta_eq_floor gives Delta_n=p exactly when 2/phi+E>=1, and JacoMaximumSet.result gives J_n={p} exactly when moreover E<2-3/phi=1/phi^4, because the fractional part of (n+2)/phi is then 2/phi+E-1 and Delta_n lies in J_n. Taking n=F_r gives E=eps_r: for r at least 3, Delta_(F_r)=F_(r-1), and J_(F_r)={F_(r-1)} exactly when r is at least 4. Taking n=F_r+F_s gives E=eps_r+eps_s: for r,s at least 3, Delta_(F_r+F_s)=F_(r-1)+F_(s-1) except at r=s=4 (order 6), and J_(F_r+F_s)={F_(r-1)+F_(s-1)} exactly when (r,s) is not (4,4) or (5,5) and any index equal to 3 is paired with 4. In particular, for r,s at least 4 the only exceptions are (4,4) for the degree and (4,4),(5,5) for the singleton, so for distinct Fibonacci orders F_r, F_s with r,s at least 4 both Delta_(F_r+F_s)=Delta_(F_r)+Delta_(F_s) and J_(F_r+F_s)={Delta_(F_r)+Delta_(F_s)}. Proposition 3.2 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, pages 10-11, takes t=F_(r-1), h=F_r and l=F_s, all at least 3 (so r at least 5, s at least 4), and asserts Delta_h=F_(r-1), J_h={v_(F_(r-1))}, Delta_(h+l)=Delta_h+Delta_l and J_(h+l)={v_(Delta_h+Delta_l)}, the last two proved there through the conjectured Theorem 2.10; on that domain the first three hold and the singleton fails exactly at h=l=5. The symmetric r,s at least 4 statement with the exceptions (3,3) and (3,3),(5,5) in terms of orders is Corollary 10 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124; the extension to indices 3 is repo-derived.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var single = All("r", Nat(), Imp(Le(D(3), r), And(Equal(Delta(Fib(r)), Fib(Pred(r))),
            Iff(Equal(J(Fib(r)), Set(Fib(Pred(r)))), Le(D(4), r)))));
        var sum = Add(Fib(r), Fib(s));
        var target = Add(Fib(Pred(r)), Fib(Pred(s)));
        var bothFour = And(Equal(r, D(4)), Equal(s, D(4)));
        var bothFive = And(Equal(r, D(5)), Equal(s, D(5)));
        var degree = All("r", Nat(), All("s", Nat(), Imp(And(Le(D(3), r), Le(D(3), s)),
            Iff(Equal(Delta(sum), target), Not(bothFour)))));
        var singleton = All("r", Nat(), All("s", Nat(), Imp(And(Le(D(3), r), Le(D(3), s)),
            Iff(Equal(J(sum), Set(target)), And(Not(bothFour), And(Not(bothFive),
                And(Imp(Equal(r, D(3)), Equal(s, D(4))), Imp(Equal(s, D(3)), Equal(r, D(4))))))))));
        var additive = Add(Delta(Fib(r)), Delta(Fib(s)));
        var distinct = All("r", Nat(), All("s", Nat(), Imp(And(Le(D(4), r), And(Le(D(4), s),
            new Formula.Relation(Fib(r), FormulaRelationOperator.NotEqual, Fib(s)))),
            And(Equal(Delta(sum), additive), Equal(J(sum), Set(additive))))));
        return Disp(And(single, And(degree, And(singleton, distinct))));
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
    private static Formula Set(Formula a) => Seq(Open, a, Close);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Not(Formula x) => Seq(F.Id("not"), Par(x));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
