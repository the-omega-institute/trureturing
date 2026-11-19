using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MarkedAssemblyCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary marker arity gives an exact signed exponential formula and full Sylow-order cancellation of compatible strict-prefix residuals.",
        H("Exponential coefficients of marked assemblies"), Blocks(
            Node("assembly_sum_coefficient", "The signed exponential formula",
                All("d", N(), All("V", Call("FiniteTypes"), All("C", Call("FiniteTypes"),
                All("allowed", Call("Predicate", N(), V("C")), All("S", Call("Finset", V("V")),
                All("T", Call("Finset", V("V")), All("sign", Call("Function", V("C"), Z()),
                    Eqn(Call("castQ", Call("assemblySum", V("d"), V("allowed"), V("S"), V("T"), V("sign"))),
                        Mul(Call("factorial", Call("card", V("S"))),
                            Coeff(Call("card", V("S")), Call("exp", Mul(
                                Pow(Call("castQ", Call("card", V("T"))), V("d")),
                                Call("colorSeries", V("allowed"), V("sign")))))))))))))),
                "For any natural arity d, finite V and C, arbitrary admissibility predicate and integer color weights, " +
                "the signed sum over the actual d-marker assemblies is |S|! times the ordinary degree-|S| coefficient " +
                "of exp(|T|^d P). Here P has zero constant coefficient and positive degree-j coefficient equal to " +
                "the signed sum of allowed colors at size j. All marker coordinates range independently over T, " +
                "including repetition, even when the vertex support shrinks. The proof groups the root block by " +
                "support, order, color and marker function. Its factors are the support binomial coefficient, " +
                "the support-size factorial, the color sum and |T|^d. Strong induction identifies this exact " +
                "block-removal recurrence with the formal exponential derivative recurrence. The empty assembly " +
                "gives the constant term. The existing Orders, support sums, colorSeries and signed prefix palettes " +
                "are reused from HannaA300591AssemblyCoefficients; their definitions do not impose marker arity."),
            Node("signed_prefix_residual_local_integral", "The compatible-prefix local residual",
                ResidualStatement(),
                "For every natural d and N>=1, integer sequence a, and prime p not dividing N, let P have " +
                "ordinary coefficient a(j) for 0<j<N and zero otherwise. Assume precisely the displayed lower " +
                "degree-f equations for 1<=f<N. The degree-N residual then has rational denominator coprime " +
                "to p. No restriction on d, coefficient signs, or the next source coefficient is imposed. " +
                "The finite palette realizes P, and each color has sign one or minus one independently of marker arity. Full assemblies and rooted assemblies " +
                "carry the actual simultaneous permutation actions. A rooted object has one distinguished " +
                "vertex and d independent markers; its remaining assembly retains the whole ambient marker " +
                "set, including the removed vertex. For a permutation with f>=1 fixed vertices and moved-part " +
                "signed sum M, the fixed-object subtraction equals M f! times the degree-f residual with scalar " +
                "f^d. Fixed blocks restrict every marker to the fixed vertices; moved blocks keep the original " +
                "ambient set. Signed Burnside splits the action into its positive and negative weight fibers. A Sylow p-subgroup of the " +
                "symmetric group has full order p^v_p(N!). Every element fixes a vertex since p does not divide " +
                "N; a nonidentity element fixes fewer than N vertices. Its residual therefore vanishes by the " +
                "actual lower equations. The identity moved part is uniquely empty. The resulting integer " +
                "divisibility cancels the entire factorial valuation. The zero residual and trivial Sylow group " +
                "are included. Taking d=3 supplies the cubic arithmetic step."))));

    private static Formula ResidualStatement()
    {
        var prefix = Call("prefixSeries", V("N"), V("a"));
        Formula E(Formula n) => Call("exp", Mul(Pow(Call("castQ", n), V("d")), prefix));
        Formula Previous(Formula n) => Mul(Pow(Call("castQ", n), V("d")), Coeff(Sub(n, D(1)), E(n)));
        Formula R(Formula n) => Sub(Coeff(n, E(n)), Previous(n));
        var f = V("f");
        var lower = All("f", N(), Imp(Leq(D(1), f), Imp(Lt(f, V("N")), Eqn(Coeff(f, E(f)), Previous(f)))));
        var premise = And(Leq(D(1), V("N")), And(Call("Prime", V("p")),
            And(Seq(Neg, Sp, Call("Dvd", V("p"), V("N"))), lower)));
        return All("d", N(), All("N", N(), All("a", Call("Function", N(), Z()), All("p", N(),
            Imp(premise, Call("IsRIntegralRat", V("p"), R(V("N"))))))));
    }
    private static DocumentBlock Node(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("marked-" + name.Replace('_', '-')),
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
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Seq(Open, a, Close), b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
}
