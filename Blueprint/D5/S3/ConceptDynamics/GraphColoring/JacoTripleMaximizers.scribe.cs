using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoTripleMaximizersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite linear Jaco graphs with exactly three maximum-degree vertices are those of order 3j+1+2b_j for j at least one, with gaps 3 or 5.",
        H("Jaco graphs with three maximum-degree vertices"),
        Blocks(
            Node("jaco-triple-orders", "The order recurrence p_j", "orders",
                Disp(And(Equal(Call("p", D(0)), D(1)), All("j", Nat(), Equal(Call("p", Add(F.Id("j"), D(1))),
                    Add(Add(Call("p", F.Id("j")), D(3)), Multiply(D(2), Par(Subtract(B(Add(F.Id("j"), D(1))), B(F.Id("j")))))))))),
                "orders 0=1 and orders(j+1)=orders j+3+2(b_(j+1)-b_j), where b_i=beattyOut i=floor((i+1)/phi); this is the recurrence p_(j+1)=p_j+3+2(floor((j+2)/phi)-floor((j+1)/phi)) with seed p_0=1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("jaco-triple-result", "Orders with three maximum-degree vertices", "result", ResultFormula(),
                "Write J_n for the set of labels of maximum-degree vertices of the finite linear Jaco graph J_n(1) and b_i=floor((i+1)/phi). The recurrence solves to p_j=3j+1+2b_j. For n at least two, J_n has exactly three vertices if and only if b_(n+3)=b_(n+1)+2: by JacoMaximumSet.result, |J_n|=floor(x_n phi^2)+1 with x_n the fractional part of (n+2)/phi, and x_n phi^2-2=(x_n-2/phi^2)phi^2 while b_(n+3)-b_(n+1)=2 exactly when x_n+2/phi is at least 2, that is x_n is at least 2-2/phi=2/phi^2. With f_j the fractional part of (j+1)/phi, which lies strictly between 0 and 1, the golden identity (p_j+2+i)/phi=(b_j+2j+1)+(1-f_j(2/phi-1))+i/phi puts p_j on the criterion and every order strictly between p_j and p_(j+1) off it; the gap p_(j+1)-p_j is 3 when f_j<1-1/phi and 5 when f_j>1-1/phi. Bracketing every positive order between consecutive p_j gives the exact enumeration: |J_n|=3 if and only if n=p_j for some j at least one, so the orders are p_1,p_2,...=6,9,14,19,22,...; these first values are stated, not separately machine-checked. The seed p_0=1 satisfies the Beatty criterion but J_1={1}. The sequence is strictly increasing with gaps 3 or 5, a gap 3 is always followed by a gap 5 because 2/phi>1, and two consecutive gaps 5 are always followed by a gap 3 because 3/phi<2. The recurrence is Corollary 6 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, which reformulates Conjecture 2.16.1 of Kok, Linear Jaco Graphs: A Critical Review (2016), page 73, and Patel's classification of the maximum sets posted as the solution to MathDB problem 369424; the 2016 journal text and the MathDB answer were not inspected, and no priority is claimed. The proof here is repo-derived.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var j = F.Id("j");
        var n = F.Id("n");
        var closed = All("j", Nat(), Equal(Call("p", j), Add(Add(Multiply(D(3), j), D(1)), Multiply(D(2), B(j)))));
        var criterion = All("n", Nat(), Imp(Le(D(2), n),
            Iff(Equal(Card(J(n)), D(3)), Equal(B(Add(n, D(3))), Add(B(Add(n, D(1))), D(2))))));
        var enumeration = All("n", Nat(), Iff(Equal(Card(J(n)), D(3)),
            Ex("j", Nat(), And(Le(D(1), j), Equal(Call("p", j), n)))));
        var mono = Call("StrictMono", F.Id("p"));
        var gaps = All("j", Nat(), Or(Gap(j, 3), Gap(j, 5)));
        var afterThree = All("j", Nat(), Imp(Gap(j, 3), Step(Add(j, D(1)), Add(j, D(2)), 5)));
        var afterFives = All("j", Nat(), Imp(And(Gap(j, 5), Step(Add(j, D(1)), Add(j, D(2)), 5)),
            Step(Add(j, D(2)), Add(j, D(3)), 3)));
        var seed = And(Equal(Call("p", D(0)), D(1)), And(Equal(B(Add(Call("p", D(0)), D(3))), Add(B(Add(Call("p", D(0)), D(1))), D(2))),
            new Formula.Relation(Card(J(Call("p", D(0)))), FormulaRelationOperator.NotEqual, D(3))));
        return Disp(And(closed, And(criterion, And(enumeration, And(mono, And(gaps, And(afterThree, And(afterFives, seed))))))));
    }

    private static Formula Gap(Formula j, byte d) => Step(j, Add(j, D(1)), d);
    private static Formula Step(Formula i, Formula next, byte d) => Equal(Call("p", next), Add(Call("p", i), D(d)));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula J(Formula n) => Call("jaconian", n);
    private static Formula B(Formula n) => Call("b", n);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
}
