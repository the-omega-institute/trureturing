using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasTentKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational positive semidefinite reciprocal tangent kernel", H("A rational positive semidefinite reciprocal tangent kernel"), Blocks(
            Node("K", "The tangent kernel", KernelFormula(),
                "For a positive natural cutoff L, the linear part meets the reciprocal tail at L. Lean defines the field operations at L=0 as well; positive semidefiniteness and Cauchy–Schwarz require a positive cutoff, while pointwise kernel and energy nonnegativity also hold at zero.", true),
            Node("kernel_psd", "Positive semidefiniteness", PsdFormula(),
                "A finite discrete Green identity writes the kernel as a nonnegative combination of the constant kernel and tents. Each tent is the Gram kernel of finite integer intervals. The statement allows repeated integer points and arbitrary signed rational coefficients. No integral or limiting argument is assumed."),
            Node("energy_sq_le", "Rational kernel Cauchy–Schwarz", EnergyFormula(),
                "The bilinear energy is the double sum of K(L,dist(a,b)). Positive semidefiniteness applied to a rational quadratic polynomial yields the square inequality. The two finite sets need not be disjoint."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false, bool literature = false) => Describe.Lean(
        DescribeId.Create("erdosnicolas-tentkernel-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula KernelFormula() => All("L", Nat(), All("r", Nat(),
        Eq(Call("K", V("L"), V("r")), Call("ite", Le(V("r"), V("L")),
            Sub(Div(D(2), V("L")), Div(V("r"), Pow(V("L"), D(2)))),
            Div(D(1), V("r"))))));
    private static Formula PsdFormula()
    {
        var distance=Call("natAbs",Sub(Call("x",V("i")),Call("x",V("j"))));
        var summand=Mul(Mul(Call("c",V("i")),Call("c",V("j"))),
            Call("K",V("L"),distance));
        Formula body=Imp(Lt(D(0),V("L")),Le(D(0),
            SumOver("i",V("S"),SumOver("j",V("S"),summand))));
        body=All("L",Nat(),body);
        body=All("c",Arrow(V("I"),Rat()),body);
        body=All("x",Arrow(V("I"),Int()),body);
        body=All("S",Call("Finset",V("I")),body);
        return All("I",V("Type"),body);
    }
    private static Formula EnergyFormula() => All("L", Nat(),
        All("A", SetNat(), All("B", SetNat(), Imp(Lt(D(0), V("L")),
            Le(Pow(Call("energy", V("L"), V("A"), V("B")), D(2)),
                Mul(Call("energy", V("L"), V("A"), V("A")),
                    Call("energy", V("L"), V("B"), V("B"))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp,
            Seq(Open, body, Close));
    private static Formula SetNat() => Call("Finset", Nat());
}
