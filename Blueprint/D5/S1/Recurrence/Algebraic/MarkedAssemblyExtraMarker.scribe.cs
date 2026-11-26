using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MarkedAssemblyExtraMarkerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One extra ambient marker on the pointed assembly increases the coefficient multiplier by one power.",
        H("Local coefficient integrality with an extra root marker"), Blocks(
            Node("signed_prefix_residual_local_integral", "The mixed-power strict-prefix residual",
                ResidualStatement(),
                "The strict prefix P has ordinary coefficient a(j) for 0<j<N and zero otherwise. " +
                "Every block has d ambient markers. The pointed object with one more marker is the " +
                "product of the usual pointed assembly with the ambient vertex type, with the diagonal " +
                "permutation action. Its weight is inherited from the assembly. A permutation with f fixed " +
                "vertices multiplies the original pointed fixed-point sum by f. Subtracting the new pointed sum " +
                "from the full sum gives the lower residual with exponential scalar f to the power d and " +
                "multiplier f to the power d+1, times f! and the common moved-block weight sum. " +
                "Each nonidentity Sylow element has between one and N-1 fixed vertices, so its residual " +
                "vanishes by the lower equations. At the identity, the moved-block sum is one. Signed " +
                "Burnside gives divisibility of the identity subtraction by the full Sylow order, cancelling " +
                "the entire p-adic valuation of N!."))));

    private static Formula ResidualStatement()
    {
        var prefix = Call("prefixSeries", V("N"), V("a"));
        Formula E(Formula n) => Call("exp", Mul(Pow(Call("castQ", n), V("d")), prefix));
        Formula Previous(Formula n) => Mul(Pow(Call("castQ", n), Add(V("d"), D(1))), Coeff(Sub(n, D(1)), E(n)));
        Formula R(Formula n) => Sub(Coeff(n, E(n)), Previous(n));
        var f = V("f");
        var lower = All("f", N(), Imp(Leq(D(1), f), Imp(Lt(f, V("N")), Eqn(Coeff(f, E(f)), Previous(f)))));
        var premise = And(Leq(D(1), V("N")), And(Call("Prime", V("p")),
            And(Seq(Neg, Sp, Call("Dvd", V("p"), V("N"))), lower)));
        return All("d", N(), All("N", N(), All("a", Call("Function", N(), Z()), All("p", N(),
            Imp(premise, Leq(D(0), Call("padicValRat", V("p"), R(V("N")))))))));
    }
    private static DocumentBlock Node(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("extra-marker-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name))) : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Seq(Open, a, Close), b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
}
