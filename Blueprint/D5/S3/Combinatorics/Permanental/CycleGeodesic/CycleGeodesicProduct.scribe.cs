using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental.CycleGeodesic;

internal sealed class CycleGeodesicProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/rivin2026permanents");
    private static readonly LibraryNoteRef Han = LibraryNoteRef.Create("D5/L/Fourier/han2000scott");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal cycle-geodesic permanent admits an exact product over the roots.", H("CycleGeodesicProduct"),
        Blocks(
            Node("gamma", "gamma", Disp(All("n", Naturals(), All("t", Reals(), All("j", Call("Fin", F.Id("n")), All("l", Call("Fin", F.Id("n")), Equal(Call("gamma", F.Id("n"), F.Id("t"), F.Id("j"), F.Id("l")), Frac(Sub(Apply(Qualified("Complex", "exp"), Mul(Cast(Mul(Mul(D(2), Qualified("Real", "pi")), F.Id("t")), Complexes()), Qualified("Complex", "I"))), D(1)), Mul(Cast(F.Id("n"), Complexes()), Sub(Apply(Qualified("Complex", "exp"), Mul(Cast(Frac(Mul(Mul(D(2), Qualified("Real", "pi")), Add(Sub(Cast(Call("val", F.Id("l")), Reals()), Cast(Call("val", F.Id("j")), Reals())), F.Id("t"))), Cast(F.Id("n"), Reals())), Complexes()), Qualified("Complex", "I"))), D(1)))))))))),
                Blocks(Paragraph(Text("Page 7, Section 4.1: \"The geodesic γ(t) is therefore a circulant matrix with explicit entries\". The displayed expression is Eq. (circulant). The indices belong to Fin n and are cast before subtraction."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("productvalue", "productValue", Disp(All("n", Naturals(), All("z", Complexes(), Equal(Call("productValue", F.Id("n"), F.Id("z")), Mul(Pow(Pow(Cast(F.Id("n"), Complexes()), Negate(D(1))), F.Id("n")), ProdOver("k", Call("Fin", F.Id("n")), Add(Sub(Cast(F.Id("n"), Complexes()), Cast(Call("val", F.Id("k")), Complexes())), Mul(Cast(Call("val", F.Id("k")), Complexes()), F.Id("z"))))))))),
                Blocks(Paragraph(Text("The polynomial product packages the exact finite-dimensional permanent value."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Han)),
            Node("productformula", "ProductFormula", Disp(IffTo(F.Id("ProductFormula"), All("n", Naturals(), All("t", Reals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(LtTo(D(0), F.Id("t")), ImpliesTo(LtTo(F.Id("t"), D(1)), Equal(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), F.Id("t"))), Call("productValue", F.Id("n"), Apply(Qualified("Complex", "exp"), Mul(Cast(Mul(Mul(D(2), Qualified("Real", "pi")), F.Id("t")), Complexes()), Qualified("Complex", "I")))))))))))),
                Blocks(Paragraph(Text("The product identity is stated for every positive dimension and every interior parameter."))), DescribeRole.Definition, AssessedProvenance.FromLiterature(Han)),
            Node("q-midpoint", "q_midpoint", Disp(Equal(Apply(Qualified("Complex", "exp"), Mul(Cast(Mul(Mul(D(2), Qualified("Real", "pi")), Frac(D(1), D(2))), Complexes()), Qualified("Complex", "I"))), Negate(D(1)))),
                Blocks(Paragraph(Text("The midpoint exponential is minus one."))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("product-formula", "product_formula", Disp(All("n", Naturals(), All("t", Reals(), ImpliesTo(LeqTo(D(1), F.Id("n")), ImpliesTo(LtTo(D(0), F.Id("t")), ImpliesTo(LtTo(F.Id("t"), D(1)), Equal(Apply(Qualified("Matrix", "permanent"), Call("gamma", F.Id("n"), F.Id("t"))), Call("productValue", F.Id("n"), Apply(Qualified("Complex", "exp"), Mul(Cast(Mul(Mul(D(2), Qualified("Real", "pi")), F.Id("t")), Complexes()), Qualified("Complex", "I"))))))))))),
                Blocks(Paragraph(Text("Han's generalized Scott identity supplies this finite product in the literature. Here the Cauchy permanent is expressed as a Gaudin determinant, whose weighted Vandermonde action is a cyclic permutation times a diagonal matrix."))), DescribeRole.Theorem, AssessedProvenance.FromLiterature(Han))), []));

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
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula ProdOver(string n, Formula t, Formula b) =>
        Parenthesized(Seq(Prod, Underscore, Grp(F.Id(n), Colon, t), Sp, Parenthesized(b)));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
