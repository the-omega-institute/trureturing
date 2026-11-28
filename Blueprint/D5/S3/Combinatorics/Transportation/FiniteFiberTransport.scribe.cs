using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class FiniteFiberTransportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Semigroups/atserias2025witnesses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conical binary refinement is equivalent to exact transportation over every finite pair of fibers.",
        H("Finite-Fiber Transportation in Commutative Monoids"),
        Blocks(Describe.Lean(
            DescribeId.Create("conical-refinement-finite-fiber-transport"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/FiniteFiberTransport.conical_refinement_iff_finite_fiber_transport"),
            H("The exact transportation equivalence"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("K is any additive commutative monoid. Conicality means that x+y=0 implies x=0 and y=0. Binary refinement means that every equality a+b=c+d admits four entries r,s,t,u with r+s=a, t+u=b, r+t=c and s+u=d. These are exactly the two clauses on the left of the equivalence.")),
                Paragraph(Text("On the right, A and B range over all finite types, including empty types, and Z ranges over arbitrary types. The maps f:A to Z and g:B to Z and the weights p:A to K and q:B to K are arbitrary. In the formula, fiberSum(f,p,h) denotes the original finite sum of p(a) over all a with f(a)=h, equivalently the sum over A of p(a) when f(a)=h and zero otherwise. Sum notation always uses the given monoid addition and its zero.")),
                Paragraph(Text("If the two fiber sums agree for every h in Z, there exists one matrix m:A to B to K. It is zero whenever the labels disagree; every row sums to its prescribed p(a), and every column sums to its prescribed q(b). Equality is exact. No order, cancellation, multiplication, division, normalization, nonzero individual weight, nonempty carrier, nontrivial monoid or finite label type is required.")),
                Paragraph(Text("For the construction, binary refinement first splits a finite family into two families with prescribed totals. Induction on the row set then builds a matrix for any two equal finite totals. Conicality makes every term of a vanishing sum zero and supplies both empty-set base cases. For each label, apply this construction to the two families with all other labels replaced by zero. Choose a matrix for every label. The final entry in row a is taken from the matrix for f(a). A mismatched column of that matrix vanishes. For a fixed column b, each summand can therefore be compared with the matrix for g(b), yielding its exact column total. No sum over Z occurs.")),
                Paragraph(Text("Conversely, use two rows and no columns with a single label to force each summand of x+y=0 to vanish. Use two rows and two columns with a single label to obtain the four refinement entries. Universe lifts of the two-element and empty types preserve the quantified carrier universes.")),
                Paragraph(Text("The finite transportation theorem and fiberwise consistency construction are known results in Atserias and Kolaitis, Theorem 1 and Section 6. The formulation here also makes empty carriers and the converse conicality clause explicit. The Section 8 classification of monoids admitting largest-support witnesses remains a separate question; this theorem neither classifies such supports nor asserts uniqueness or pointwise maximality."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SumAt(string name, Formula carrier, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Sp, InMacro, Sp, carrier)), Sp, body);
    private static Formula Instance(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Comma, Sp, body);

    private static Formula Statement()
    {
        Formula k=V("K"), a=V("a"), b=V("b"), c=V("c"), d=V("d");
        Formula x=V("x"), y=V("y"), r=V("r"), s=V("s"), t=V("t"), u=V("u");
        Formula conical = All("x", k, All("y", k,
            Imp(Eq(Add(x,y),D(0)), And(Eq(x,D(0)),Eq(y,D(0))))));
        Formula matrix = And(Eq(Add(r,s),a), And(Eq(Add(t,u),b),
            And(Eq(Add(r,t),c),Eq(Add(s,u),d))));
        Formula binary = All("a", k, All("b", k, All("c", k, All("d", k,
            Imp(Eq(Add(a,b),Add(c,d)), Some("r",k,Some("s",k,Some("t",k,Some("u",k,matrix)))))))));
        Formula ac=V("A"), bc=V("B"), z=V("Z");
        Formula f=V("f"), g=V("g"), p=V("p"), q=V("q"), m=V("m"), h=V("h");
        Formula agree=All("h",z,Eq(Call("fiberSum",f,p,h),Call("fiberSum",g,q,h)));
        Formula vanish=All("a",ac,All("b",bc,
            Imp(Ne(Call("f",a),Call("g",b)),Eq(Call("m",a,b),D(0)))));
        Formula rows=All("a",ac,Eq(SumAt("b",bc,Call("m",a,b)),Call("p",a)));
        Formula cols=All("b",bc,Eq(SumAt("a",ac,Call("m",a,b)),Call("q",b)));
        Formula witness=Some("m",Arrow(ac,Arrow(bc,k)),And(vanish,And(rows,cols)));
        Formula transport=All("A",V("Type"),All("B",V("Type"),All("Z",V("Type"),
            Instance("Fintype",ac,Instance("Fintype",bc,
                All("f",Arrow(ac,z),All("g",Arrow(bc,z),All("p",Arrow(ac,k),All("q",Arrow(bc,k),
                    Imp(agree,witness))))))))));
        return All("K",V("Type"),Instance("AddCommMonoid",k,
            Logic(And(conical,binary),FormulaLogicOperator.Iff,transport)));
    }
}
