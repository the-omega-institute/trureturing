using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoDegreeShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite linear Jaco maximum degree is b_n or b_n-1, and the order n+Delta_n then has maximum degree n or n-1.",
        H("Maximum degree, Beatty outdegree and the shifted order"),
        Blocks(
            Describe.Lean(DescribeId.Create("jaco-shift-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The two cases and the shifted order"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Write Delta_n for the maximum degree of the finite linear Jaco graph jaco n, b_n=beattyOut n=floor((n+1)/phi) for the existing Beatty outdegree, and frac n for the fractional part of (n+2)/phi. For every natural n, Delta_n=b_n exactly when frac n<1/phi, Delta_n=b_n-1 exactly when frac n>1/phi, and one of the two always holds; in the first case the order n+Delta_n has maximum degree n, in the second n-1. Theorem 2.9 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 7, states only that the order n+Delta_n has maximum degree n or n-1; its proof splits on the outdegree d+(v_n)=b_n and leaves the second case undecided between n and n-1. The case-matched values and the threshold criterion, for every natural n, are repo-derived. Proof: JacoAdditionLaw.delta_eq_floor gives Delta_n=floor((n+2)/phi)-1, and b_n=floor((n+2)/phi-1/phi). The value frac n=1/phi is impossible, since it would make (n+1)/phi an integer although (n+1)/phi is irrational. Below the threshold b_n=floor((n+2)/phi)-1, above it b_n=floor((n+2)/phi). Using 1/phi^2=1-1/phi one gets (n+Delta_n+2)/phi=n+2-(1+frac n)/phi, and (1+frac n)/phi lies in (0,1) below the threshold and in (1,2) above it, because (1+1/phi)/phi=1; so the maximum degree of the shifted order is n or n-1."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var d = Call("Delta", n);
        var b = Call("b", n);
        var x = Call("frac", n);
        var g = new Formula.Fraction(D(1), F.Id("phi"));
        var shifted = Call("Delta", Add(n, d));
        var first = Equal(d, b);
        var second = Equal(Add(d, D(1)), b);
        return Disp(All("n", Nat(), And(Or(first, second),
            And(Iff(first, Lt(x, g)),
                And(Iff(second, Lt(g, x)),
                    And(Imp(first, Equal(shifted, n)), Imp(second, Equal(Add(shifted, D(1)), n))))))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
