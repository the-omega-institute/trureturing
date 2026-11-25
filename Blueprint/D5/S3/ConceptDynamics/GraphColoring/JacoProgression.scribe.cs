using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoProgressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoProgression.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Along every arithmetic progression of orders the Jaco maximum degree is linear plus an explicit golden correction, and the multiples of five split into exact blocks.",
        H("Jaco maximum degrees along progressions"),
        Blocks(
            Node("jaco-prog-beta", "The golden fractional part beta_d", "beta",
                Disp(Equal(Call("beta", F.Id("d")), Call("fract", new Formula.Fraction(F.Id("d"), F.Id("phi"))))),
                "beta d is the fractional part of d/phi, so d/phi=floor(d/phi)+beta d.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-prog-start", "The block starts k_q", "blockStart",
                Disp(And(Equal(Call("k", D(0)), D(1)), All("q", Nat(), Imp(Le(D(1), F.Id("q")),
                    Equal(Call("k", F.Id("q")), Add(new Formula.Floor(Multiply(Par(Subtract(Multiply(D(5), F.Id("q")), D(1))), F.Id("phi"))), Multiply(D(3), F.Id("q")))))))),
                "blockStart 0=1 and, for q at least one, blockStart q=floor((5q-1)phi)+3q, with 5q-1 computed in the natural numbers.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-prog-block", "The block P_q", "block",
                Disp(And(Equal(Call("P", D(0)), Call("Icc", D(1), Subtract(Multiply(D(5), Call("k", D(1))), D(1)))),
                    All("q", Nat(), Imp(Le(D(1), F.Id("q")), Equal(Call("P", F.Id("q")),
                        Call("Icc", Multiply(D(5), Call("k", F.Id("q"))), Subtract(Multiply(D(5), Call("k", Add(F.Id("q"), D(1)))), D(1)))))))),
                "block q is the interval of orders from 1 (for q=0) or 5 k_q (for q at least one) up to 5 k_(q+1)-1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-prog-result", "Progression law and the five-blocks", "result", ResultFormula(),
                "Write delta n for the maximum degree of the finite linear Jaco graph J_n(1), alpha=sqrt(5)-2 and beta_d=beta d. For all d and k, delta(dk)=floor(d/phi)k+floor(beta_d k+alpha): JacoAdditionLaw.delta_eq_floor gives delta n=floor((n+2)/phi)-1, and (dk+2)/phi=floor(d/phi)k+1+(beta_d k+alpha) because 2/phi=1+alpha. For d at least one, beta_d lies strictly between 0 and 1 since d/phi is irrational, and for k at least one and every integer q the correction equals q exactly when max(1, ceil((q-alpha)/beta_d))<=k<ceil((q+1-alpha)/beta_d). For d=5, floor(5/phi)=3 and beta_5=5phi-8, whose inverse is 3+5phi, so (q-alpha)/beta_5=3q-1+(5q-1)phi and its ceiling is k_q=floor((5q-1)phi)+3q for q at least one. The blocks P_0=[1,5k_1-1] and P_q=[5k_q,5k_(q+1)-1] are nonempty, lie in the positive integers and partition them, and 5k in P_q gives delta(5k)=3k+q. Since k_1=9, k_2=20 and k_3=31, the first blocks are [1,44], [45,99] and [100,154]; these values are stated, not separately machine-checked. The first open problem on printed page 11 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, records Delta(J_5k(1))=3k on P_0=[1,44] and 3k+1 on P_1=[45,99], leaves the right end of P_2 open, and asks for a partitioning that closes the pattern; the blocks P_q above answer it, and the general progression law is repo-derived. Possible answers posted on MathDB were not inspected, so no priority is claimed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var q = F.Id("q");
        var b = Call("beta", d);
        var corr = new Formula.Floor(Add(Multiply(b, k), F.Id("alpha")));
        var law = All("d", Nat(), All("k", Nat(), Equal(Delta(Multiply(d, k)),
            Add(Multiply(new Formula.Floor(new Formula.Fraction(d, F.Id("phi"))), k), corr))));
        var range = All("d", Nat(), All("k", Nat(), All("q", Int(), Imp(And(Le(D(1), d), Le(D(1), k)),
            Iff(Equal(corr, q), And(Le(Call("max", D(1), Ceil(new Formula.Fraction(Subtract(q, F.Id("alpha")), b))), k),
                Lt(k, Ceil(new Formula.Fraction(Subtract(Add(q, D(1)), F.Id("alpha")), b)))))))));
        var starts = All("q", Nat(), Imp(Le(D(1), q), Equal(Ceil(new Formula.Fraction(Subtract(q, F.Id("alpha")), Call("beta", D(5)))), Call("k", q))));
        var partition = All("m", Nat(), Imp(Le(D(1), F.Id("m")), Call("ExistsUnique", F.Id("q"), Call("mem", F.Id("m"), Call("P", q)))));
        var blocks = All("q", Nat(), All("k", Nat(), Imp(Call("mem", Multiply(D(5), k), Call("P", q)),
            Equal(Delta(Multiply(D(5), k)), Add(Multiply(D(3), k), q)))));
        var unit = All("d", Nat(), Imp(Le(D(1), d), And(Lt(D(0), b), Lt(b, D(1)))));
        var five = And(Equal(new Formula.Floor(new Formula.Fraction(D(5), F.Id("phi"))), D(3)),
            Equal(Call("beta", D(5)), Subtract(new Formula.Fraction(D(5), F.Id("phi")), D(3))));
        var positive = All("q", Nat(), All("m", Nat(), Imp(Call("mem", F.Id("m"), Call("P", q)), Le(D(1), F.Id("m")))));
        var nonempty = All("q", Nat(), Call("Nonempty", Call("P", q)));
        return Disp(And(law, And(unit, And(five, And(range, And(starts, And(partition,
            And(positive, And(nonempty, blocks)))))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Delta(Formula n) => Call("delta", n);
    private static Formula Ceil(Formula x) => Call("ceil", x);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
