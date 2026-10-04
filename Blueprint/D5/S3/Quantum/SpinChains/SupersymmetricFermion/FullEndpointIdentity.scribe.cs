using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class FullEndpointIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full occupation-space calculation of the period-three boundary sum rule.",
        H("Supersymmetric fermion chain: full endpoint identity"),
        Blocks(
            Paragraph(Text("Nat, Real and Complex denote the natural, real and complex numbers. Fin(N) denotes the finite index type; val is its natural value. mk displays a Fin value with its proof component suppressed. All finite-type sums range over the displayed type; subtraction in Nat is truncated at zero. mod is natural remainder, smul is scalar multiplication and asReal retains the real scalar annotation. fullQ, fullR, chainG, fullPAt and blockDiagonal are the chain definitions. symOp(A)=A+adjoint(A), with the matrix conjugate transpose. finTwoReindex and boolReindex transport matrices in opposite directions through finTwoEquiv : Fin 2 ≃ Bool, applied pointwise to occupation configurations. antiAd is the existing operator antiAd(A,B)=AB+BA. These coordinate notations do not define new Lean operators.")),
            Describe.Lean(DescribeId.Create("m1-fullendpointidentity-full-symmetrized-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity.full_symmetrized_diagonal"),
                H("Full-space period-three identity"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every N at least three and divisible by three, and all real a,b,c, localization of the cubic products and cancellation of the hopping currents leave precisely the displayed diagonal terms. The statement is an identity on the full Boolean occupation space; the hard-core transport and occupation telescope give the endpoint identity in the next module."))),
                DescribeRole.Theorem))));

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Bin(Formula left, FormulaBinaryOperator op, Formula right) =>
        new Formula.Binary(P(left), op, P(right));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Statement()
    {
        var n = N("N"); var a = N("a"); var b = N("b"); var c = N("cc"); var k = N("k");
        var coupling = P(Seq(P(Seq(N("i"), Colon, Call("Fin", n))), Mapsto,
            Call("chainG", a, b, c, Call("val", N("i")))));
        var q = Call("fullQ", coupling);
        var r = Call("fullR", n, a, b, c);
        var left = Call("symOp", Call("boolReindex", Call("antiAd",
            Call("finTwoReindex", q), Call("finTwoReindex", r))));
        var scalar = Seq(Bin(Bin(D(2), FormulaBinaryOperator.Multiply, new Formula.Power(P(a), D(2))),
            FormulaBinaryOperator.Multiply, new Formula.Power(P(c), D(2))), Colon, N("Real"));
        var boundary = Call("smul", P(Seq(Call("asReal", P(scalar)), Colon, N("Complex"))),
            Bin(Call("fullPAt", n, D(1)), FormulaBinaryOperator.Subtract,
                Call("fullPAt", n, Bin(n, FormulaBinaryOperator.Subtract, D(2)))));
        var index = P(Seq(Call("mk", Call("val", k)), Colon, Call("Fin", n)));
        var sumType = Call("Fin", Bin(n, FormulaBinaryOperator.Subtract, D(2)));
        var sum = Seq(Sum, Underscore, Grp(Seq(k, InMacro, sumType)),
            P(Call("blockDiagonal", a, b, c, index)));
        var conclusion = Eq(left, Bin(boundary, FormulaBinaryOperator.Add, sum));
        var quantified = All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), conclusion)));
        var divisible = new Formula.Logic(P(Eq(Call("mod", n, D(3)), D(0))),
            FormulaLogicOperator.Implies, P(quantified));
        var length = new Formula.Logic(P(new Formula.Relation(D(3),
            FormulaRelationOperator.LessThanOrEqual, n)), FormulaLogicOperator.Implies, P(divisible));
        return Disp(All("N", N("Nat"), length));
    }
}
