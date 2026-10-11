using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental.CycleGeodesic;

internal sealed class GaudinPermanentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/rivin2026permanents");
    private static readonly LibraryNoteRef Faribault = LibraryNoteRef.Create("D5/L/Fourier/faribaultschuricht2012gaudin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cauchy permanent equals a Gaudin determinant by interpolation and induction.", H("GaudinPermanent"),
        Blocks(
            Node("cauchy", "cauchy", Disp(All("n", Naturals(), All("x", Arrow(Call("Fin", F.Id("n")), Complexes()), All("y", Arrow(Call("Fin", F.Id("n")), Complexes()), All("i", Call("Fin", F.Id("n")), All("j", Call("Fin", F.Id("n")), Equal(Call("cauchy", F.Id("x"), F.Id("y"), F.Id("i"), F.Id("j")), Pow(Sub(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("y"), F.Id("j"))), Negate(D(1)))))))))),
                Blocks(Paragraph(Text("The reciprocal-difference matrix uses zero-based row and column parameters."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Faribault)),
            Node("baryderivative", "baryDerivative", Disp(All("V", F.Id("Type"), Seq(Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp), Seq(OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp), All("x", Arrow(F.Id("V"), Complexes()), All("i", F.Id("V"), All("j", F.Id("V"), Equal(Call("baryDerivative", F.Id("x"), F.Id("i"), F.Id("j")), IfThenElse(Equal(F.Id("i"), F.Id("j")), Seq(Sum, Underscore, Grp(Seq(F.Id("k"), Sp, InMacro, Sp, Apply(Qualified("Finset", "erase"), Qualified("Finset", "univ"), F.Id("i")))), Sp, Parenthesized(Pow(Sub(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("x"), F.Id("k"))), Negate(D(1))))), Pow(Sub(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("x"), F.Id("j"))), Negate(D(1))))))))))),
                Blocks(Paragraph(Text("The diagonal is the sum of the reciprocal node differences; the off-diagonal entries are their individual reciprocals."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Faribault)),
            Node("gaudin", "gaudin", Disp(All("V", F.Id("Type"), All("W", F.Id("Type"), Seq(Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp), Seq(OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp), Seq(OpenBracket, Call("Fintype", F.Id("W")), CloseBracket, Sp), All("x", Arrow(F.Id("V"), Complexes()), All("y", Arrow(F.Id("W"), Complexes()), Equal(Call("gaudin", F.Id("x"), F.Id("y")), Sub(Apply(Qualified("Matrix", "diagonal"), LambdaOf("i", F.Id("V"), SumOver("j", F.Id("W"), Pow(Sub(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("y"), F.Id("j"))), Negate(D(1)))))), Call("baryDerivative", F.Id("x")))))))))),
                Blocks(Paragraph(Text("Subtracting the barycentric differentiation matrix gives the Gaudin matrix in the reciprocal-difference sign convention."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Faribault)),
            Node("gaudin-mulvec", "gaudin_mulVec", Disp(All("V", F.Id("Type"), All("W", F.Id("Type"), Seq(Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp), Seq(OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp), Seq(OpenBracket, Call("Fintype", F.Id("W")), CloseBracket, Sp), All("x", Arrow(F.Id("V"), Complexes()), All("y", Arrow(F.Id("W"), Complexes()), All("p", Seq(Complexes(), OpenBracket, F.Id("X"), CloseBracket), ImpliesTo(And(Parenthesized(Apply(Qualified("Function", "Injective"), F.Id("x"))), Parenthesized(LtTo(Apply(Qualified("Polynomial", "degree"), F.Id("p")), Apply(Qualified("Fintype", "card"), F.Id("V"))))), Equal(Apply(Qualified("Matrix", "mulVec"), Call("gaudin", F.Id("x"), F.Id("y")), LambdaOf("i", F.Id("V"), Mul(Apply(Qualified("Lagrange", "nodalWeight"), Qualified("Finset", "univ"), F.Id("x"), F.Id("i")), Apply(Qualified("Polynomial", "eval"), Apply(F.Id("x"), F.Id("i")), F.Id("p"))))), LambdaOf("i", F.Id("V"), Mul(Apply(Qualified("Lagrange", "nodalWeight"), Qualified("Finset", "univ"), F.Id("x"), F.Id("i")), Sub(Mul(SumOver("j", F.Id("W"), Pow(Sub(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("y"), F.Id("j"))), Negate(D(1)))), Apply(Qualified("Polynomial", "eval"), Apply(F.Id("x"), F.Id("i")), F.Id("p"))), Apply(Qualified("Polynomial", "eval"), Apply(F.Id("x"), F.Id("i")), Apply(Qualified("Polynomial", "derivative"), F.Id("p"))))))))))))))),
                Blocks(Paragraph(Text("Differentiating Lagrange interpolation describes the action on weighted polynomial evaluations."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("nodal-derivative-nonroot", "nodal_derivative_nonroot", Disp(All("V", F.Id("Type"), Seq(Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp), All("y", Arrow(F.Id("V"), Complexes()), All("z", Complexes(), ImpliesTo(All("j", F.Id("V"), NeqTo(F.Id("z"), Apply(F.Id("y"), F.Id("j")))), Equal(Apply(Qualified("Polynomial", "eval"), F.Id("z"), Apply(Qualified("Polynomial", "derivative"), Apply(Qualified("Lagrange", "nodal"), Qualified("Finset", "univ"), F.Id("y")))), Mul(Apply(Qualified("Polynomial", "eval"), F.Id("z"), Apply(Qualified("Lagrange", "nodal"), Qualified("Finset", "univ"), F.Id("y"))), SumOver("j", F.Id("V"), Pow(Sub(F.Id("z"), Apply(F.Id("y"), F.Id("j"))), Negate(D(1)))))))))))),
                Blocks(Paragraph(Text("Away from every node, differentiating the nodal product gives its logarithmic derivative."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("gaudin-permanent", "gaudin_permanent", Disp(All("n", Naturals(), All("x", Arrow(Call("Fin", F.Id("n")), Complexes()), All("y", Arrow(Call("Fin", F.Id("n")), Complexes()), ImpliesTo(Apply(Qualified("Function", "Injective"), F.Id("x")), ImpliesTo(All("i", Call("Fin", F.Id("n")), All("j", Call("Fin", F.Id("n")), NeqTo(Apply(F.Id("x"), F.Id("i")), Apply(F.Id("y"), F.Id("j"))))), Equal(Apply(Qualified("Matrix", "det"), Call("gaudin", F.Id("x"), F.Id("y"))), Apply(Qualified("Matrix", "permanent"), Call("cauchy", F.Id("x"), F.Id("y")))))))))),
                Blocks(Paragraph(Text("The row nodes are distinct and avoid every column parameter. Column parameters may repeat. Interpolating a determinant polynomial after its top coefficient vanishes reduces the identity to the permanent expansion at the preceding order."))), DescribeRole.Theorem, AssessedProvenance.FromLiterature(Faribault))), []));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        BlockSequence prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.FromAuthor(formula), provenance,
            prose, role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula LambdaOf(string n, Formula t, Formula b) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(n), Colon, t)), Sp, Mapsto, Sp, b);
    private static Formula SumOver(string n, Formula t, Formula b) =>
        Parenthesized(Seq(Sum, Underscore, Grp(F.Id(n), Colon, t), Sp, Parenthesized(b)));
    private static Formula IfThenElse(Formula h, Formula a, Formula b) =>
        Seq(F.Id("if"), Sp, Parenthesized(h), Sp, F.Id("then"), Sp, a, Sp, F.Id("else"), Sp, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
