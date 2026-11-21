using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoMaximumSetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014finitejaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum-degree vertices of a finite linear Jaco graph form a label interval of one, two or three vertices, with exact singleton criteria.",
        H("The maximum set of a finite linear Jaco graph"),
        Blocks(
            Node("jaco-set-def", "The maximum set", "jaconian",
                Disp(Equal(J(F.Id("n")), SetOf(Equal(Call("degree", Call("jaco", F.Id("n")), F.Id("v")), P(F.Id("n")))))),
                "jaconian n is the finite set of labels of the vertices of jaco n whose ordinary degree equals the maximum degree p_n; the source calls this the Jaconian set J_n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-set-result", "Interval, size and singleton criteria", "result", ResultFormula(),
                "Write p=p_n for the maximum degree of jaco n, t=n-p, R_t=jacoRight t=t+b_t, b_i=beattyOut i=floor((i+1)/phi) and x=frac n for the fractional part of (n+2)/phi. J_1={1}. For n at least two: R_t<=n and J_n is the label interval [p,R_t], with exactly floor(x phi^2)+1 members, hence one, two or three. J_n={p} exactly when x<1/phi^2, and equivalently when n=R_p and b_(p+1)=b_p+1, when b_(n+1)=b_(n+2), and when p_(n+1)=p_n; the last equivalence says that an unchanged least maximum label at the next order happens exactly after a unique maximum. At a unique maximum R_(p+1)=n+2, b_n=p, the last vertex v_n has degree n-p, and J_(n+1) is {p,p+1} or {p,p+1,p+2}. Proof: by the existing degree formula deg(v_i)=min(i,n-b_i), a vertex attains p exactly when p<=i and b_i<=t, and the existing Beatty threshold turns b_i<=t into i<=R_t. JacoAdditionLaw.delta_eq_floor gives p=F-1 with F=floor((n+2)/phi), and golden-ratio identities give R_t=p+floor(x phi^2), R_p=n+1+floor(-x phi), b_(p+1)-b_p=floor(1/phi-x phi)-floor(-x phi), b_(n+1)=F and b_(n+2)=p_(n+1)+1=F+floor(x+1/phi). Since phi is irrational, x avoids 0, 1/phi^2 and 1/phi, and every clause is decided by the side of 1/phi^2 on which x falls. The request credits this description to Patel's solution posted on MathDB; that page refuses automated fetches and was not inspected here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("jaco-set-strict", "Strict outdegree growth and its converse", "strict_out_singleton", StrictFormula(),
                "For n at least two, b_(n-1)<b_n<b_(n+1) forces J_n={b_n}: the right inequality gives x<1/phi, the left one then gives x<2/phi-1<1/phi^2, so the maximum is unique and b_n=p. This is the implication of Lemma 2.2 (Conjectured) of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 4. The converse, which the source does not assert, fails at order five: J_5={3} although b_4=b_5=3.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var p = P(n);
        var r = Call("jacoRight", Subtract(n, p));
        var x = Call("frac", n);
        var single = Equal(J(n), Set(p));
        var interval = And(Le(r, n), And(Equal(J(n), Call("Icc", p, r)),
            Equal(Call("card", J(n)), Add(new Formula.Floor(Multiply(x, new Formula.Power(F.Id("phi"), D(2)))), D(1)))));
        var criteria = And(Iff(single, Lt(x, new Formula.Fraction(D(1), new Formula.Power(F.Id("phi"), D(2))))),
            And(Iff(single, And(Equal(n, Call("jacoRight", p)), Equal(B(Add(p, D(1))), Add(B(p), D(1))))),
                And(Iff(single, Equal(B(Add(n, D(1))), B(Add(n, D(2))))), Iff(single, Equal(P(Add(n, D(1))), p)))));
        var consequences = Imp(single, And(Equal(Call("jacoRight", Add(p, D(1))), Add(n, D(2))),
            And(Equal(B(n), p), Or(Equal(J(Add(n, D(1))), Call("Icc", p, Add(p, D(1)))),
                Equal(J(Add(n, D(1))), Call("Icc", p, Add(p, D(2))))))));
        return Disp(And(Equal(J(D(1)), Set(D(1))),
            All("n", Nat(), Imp(Le(D(2), n), And(interval, And(criteria, consequences))))));
    }

    private static Formula StrictFormula()
    {
        var n = F.Id("n");
        return Disp(And(All("n", Nat(), Imp(Le(D(2), n),
                Imp(And(Lt(B(Subtract(n, D(1))), B(n)), Lt(B(n), B(Add(n, D(1))))), Equal(J(n), Set(B(n)))))),
            And(Equal(J(D(5)), Set(D(3))), Equal(B(D(4)), B(D(5))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula J(Formula n) => Call("jaconian", n);
    private static Formula P(Formula n) => Call("maxDegree", Call("jaco", n));
    private static Formula B(Formula n) => Call("beattyOut", n);
    private static Formula Set(Formula a) => Seq(Open, a, Close);
    private static Formula SetOf(Formula body) => Seq(Open, F.Id("v"), Colon, Sp, body, Close);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
