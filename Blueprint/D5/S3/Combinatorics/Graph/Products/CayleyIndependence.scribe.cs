using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class CayleyIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = I("V"); var w = I("W"); var g = I("G"); var h = I("H"); var i = I("I"); var r = I("R");
        var support = All("p", C("Prod", v, w), Imp(C("Mem", I("p"), i), C("Mem", C("fst", I("p")), r)));
        var bound = All("V", C("Type"), All("W", C("Type"), Inst("Finite", w,
            All("G", C("SimpleGraph", v), All("H", C("SimpleGraph", w),
                All("I", C("Finset", C("Prod", v, w)), All("R", C("Finset", v),
                    Imp(And(C("IsIndepSet", C("boxProd", g, h), i), support),
                        Le(C("card", i), Mul(C("card", r), C("indepNum", h)))))))))));
        var s = I("S"); var a = I("A"); var cay = C("addCayley", s);
        var equality = Groups(Eq(C("indepNum", C("boxProd", cay, cay)), Mul(C("FintypeCard", a), C("indepNum", cay))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Independent sets have a per-row upper bound; a difference-set construction attains that bound in finite abelian Cayley squares.",
            H("Independence in Cartesian Cayley squares"), Blocks(
                Node("CayleyIndependence", "layer-bound", "Counting independent vertices by rows", "card_le_layer_bound", bound,
                    "In a Cartesian product G □ H with H finite, the second coordinates in each fixed row form an independent set of H. If every selected first coordinate belongs to the finite set R, summing the row bounds gives |I| ≤ |R| alpha(H). The first factor may be infinite; both factors may be empty or disconnected."),
                Node("CayleyIndependence", "cayley-square", "The full abelian square equality", "indepNum_addCayley_square", equality,
                    "Let A be any finite additive abelian group, and let S avoid zero and be closed under negation. The native Cayley adjacency is exactly y-x in S. For a maximum independent set B, the pairs (x,x+b), with x in A and b in B, form an independent set in the Cartesian square. Injectivity gives |A||B| vertices and attains the row bound. Connectedness is unnecessary; the trivial group, an empty connection set, and self-inverse steps are included."))));
    }
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Groups(Formula b)
    {
        var a = I("A"); var s = I("S"); var z = I("z");
        var inverse = All("z", a, Imp(C("Mem", z, s), C("Mem", C("neg", z), s)));
        var allowed = And(Not(C("Mem", D(0), s)), inverse);
        return All("A", C("Type"), Inst("Fintype", a, Inst("AddCommGroup", a,
            All("S", C("Set", a), Imp(allowed, b)))));
    }
    private static DocumentBlock Node(string module, string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Products/" + module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
