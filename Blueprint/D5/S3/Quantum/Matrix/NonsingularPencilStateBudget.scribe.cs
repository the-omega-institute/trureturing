using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class NonsingularPencilStateBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/NonsingularPencilStateBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonsingular Hermitian pencils control every positive complex-linear reading on the same matrix algebra.",
        H("Strict budgets and the zero-mass boundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("nonsingular-pencil"),
                DeclarationHandle.Create(Prefix + "pencil"), H("The two-parameter pencil"),
                StatementSource.FromAuthor(Disp(PencilDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite square complex matrices E,K,G and real parameters p,q, "
                    + "P(E,K,G,p,q)=E+(p²+q²)I−2pK−2qG. All factors and every reading belong to the same matrix algebra."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonsingular-pencil-state-budget"),
                DeclarationHandle.Create(Prefix + "strict_budget"), H("Every positive functional, with its original mass"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume E is positive definite, K and G are Hermitian, and the determinant "
                        + "of P(E,K,G,p,q) is nonzero for every real p,q. Every positive complex-linear functional phi "
                        + "has real readings on E,K,G. If m=Re phi(I)>0, then Re phi(G)²+Re phi(K)²<m Re phi(E). "
                        + "If m=0, phi is the zero functional and the corresponding non-strict budget is equality. "
                        + "No normalization, density-matrix representation, or restriction of the functional family is imposed.")),
                    Paragraph(Text("The positive-definite locus of a continuous Hermitian family is open. "
                        + "When its determinant never vanishes it agrees with the positive-semidefinite locus, which is closed. "
                        + "The real parameter plane is connected and P(E,K,G,0,0)=E, so every pencil value is positive definite. "
                        + "A positive definite matrix dominates a positive scalar multiple of the unit. "
                        + "Apply the original positive functional at p=Re phi(K)/m and q=Re phi(G)/m. "
                        + "The operator norm of a positive functional is its unit value, which also proves the zero-mass assertion.")),
                    Paragraph(Text("The compact-sphere openness argument is adapted from TauCetiProject/TauCeti, "
                        + "commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d, TauCeti/Analysis/Matrix/PosDef.lean. "
                        + "The spectral, connectedness, and positive-functional ingredients are classical. "
                        + "This theorem supplies a conditional bridge: a concrete table still has to establish "
                        + "the nonvanishing determinant on the entire real plane and positivity of E. "
                        + "It does not establish a total response, a complete PB family, or physical source contracts."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Apply(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket,t,CloseBracket,Sp,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a,b);
    private static Formula Square(Formula a) => new Formula.Power(a,D(2));
    private static Formula Real => Call("Real");
    private static Formula Mat => Call("Matrix",V("n"),V("n"),Call("Complex"));
    private static Formula One => Call("one",Mat);
    private static Formula Reading(string a) => Call("re",Apply(V("phi"),a=="I"?One:V(a)));
    private static Formula Sum => Add(Square(Reading("G")),Square(Reading("K")));
    private static Formula Bound => Mul(Reading("I"),Reading("E"));
    private static Formula WithIndex(Formula b) => All("n",Seq(Call("Type"),Star),
        Instance(Call("Fintype",V("n")),Instance(Call("DecidableEq",V("n")),b)));
    private static Formula WithMatrices(Formula b) => All("E",Mat,All("K",Mat,All("G",Mat,b)));
    private static Formula P => Call("pencil",V("E"),V("K"),V("G"),V("p"),V("q"));

    private static Formula PencilDefinition() => WithIndex(WithMatrices(All("p",Real,All("q",Real,
        Equal(P,Sub(Sub(Add(V("E"),Call("smul",Add(Square(V("p")),Square(V("q"))),One)),
            Call("smul",Mul(D(2),V("p")),V("K"))),Call("smul",Mul(D(2),V("q")),V("G"))))))));

    private static Formula Statement()
    {
        var readings = And(Equal(Call("im",Apply(V("phi"),V("E"))),D(0)),
            And(Equal(Call("im",Apply(V("phi"),V("K"))),D(0)),
                Equal(Call("im",Apply(V("phi"),V("G"))),D(0))));
        var positive = Imp(new Formula.Relation(D(0),FormulaRelationOperator.LessThan,Reading("I")),
            new Formula.Relation(Sum,FormulaRelationOperator.LessThan,Bound));
        var zero = Imp(Equal(Reading("I"),D(0)),And(Equal(V("phi"),D(0)),Equal(Sum,Bound)));
        var nonzero = All("p",Real,All("q",Real,
            new Formula.Relation(Call("det",P),FormulaRelationOperator.NotEqual,D(0))));
        return WithIndex(WithMatrices(Imp(Call("PosDef",V("E")),Imp(Call("IsHermitian",V("K")),
            Imp(Call("IsHermitian",V("G")),Imp(nonzero,
                All("phi",Call("PositiveLinearMap",Call("Complex"),Mat,Call("Complex")),
                    And(readings,And(positive,zero)))))))));
    }
}
