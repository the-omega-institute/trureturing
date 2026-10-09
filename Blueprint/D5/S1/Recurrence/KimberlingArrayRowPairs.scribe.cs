using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class KimberlingArrayRowPairsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/KimberlingArrayRowPairs.";

    public DocumentDefinition Create()
    {
        var n = F.Id("n"); var i = F.Id("i");
        var N = F.Id("N");
        var z = F.Id("z"); var s = F.Id("s"); var r = F.Id("r");
        var phi = T("goldenRatio");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden integer units have signed integral powers and an oriented small-unit description.",
            H("Golden units for Kimberling row intersections"),
            Blocks(
            Node("row", "Golden power rows", "row",
                Disp(All("i", T("Nat"), All("N", T("Nat"), Iff(Mem(N, C("row", i)), Ex("k", T("Nat"), And(Le(D(1), F.Id("k")), Eq(N, new Formula.Floor(Mul(F.Id("k"), Pow(phi, i)))))))))),
                "Row i consists of the natural floors of positive integral multiples of the ith golden power.", DescribeRole.Definition),
            Node("lucas", "Lucas trace", "lucas",
                Disp(All("n", T("Nat"), Eq(C("lucas", n), C("toNat", C("goldenLucas", n))))),
                "The natural Lucas number is the nonnegative integral trace of the nth golden power. Its initial values are two and one.", DescribeRole.Definition),
            Node("embedding-phiunit-zpow", "Integral unit powers", "embedding_phiUnit_zpow",
                Disp(All("s", T("Int"), Eq(C("embedding", C("coe", Pow(T("phiUnit"), s))), Pow(phi, s)))),
                "The distinguished unit evaluates to the golden ratio for all integral exponents.", DescribeRole.Theorem),
            Node("phiunit-neg-nat", "Inverse powers", "phiUnit_neg_nat",
                Disp(All("r", T("Nat"), Eq(C("coe", Pow(T("phiUnit"), Sub(D(0), r))), Mul(Pow(Sub(D(0), D(1)), r), C("conj", Pow(T("phi"), r)))))),
                "Inverse powers have the signed conjugate coordinates.", DescribeRole.Theorem),
            Node("golden-small-unit", "Orientation of small units", "golden_small_unit",
                Disp(All("z", T("GoldenInt"), All("i", T("Nat"), Imp(Or(Eq(C("norm", z), D(1)), Eq(C("norm", z), Sub(D(0), D(1)))), Imp(Lt(C("b", z), D(0)), Imp(Lt(C("abs", C("embedding", z)), Inv(Pow(phi, i))), Ex("r", T("Nat"), And(Le(Add(i, D(1)), r), And(Eq(z, C("conj", Pow(T("phi"), r))), Eq(C("embedding", z), Mul(Pow(Sub(D(0), D(1)), r), Inv(Pow(phi, r))))))))))))),
                "A negative golden coefficient fixes the orientation of a sufficiently small unit to the conjugate of a positive power.", DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula C(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula T(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Inv(Formula x) => C("inv", x);

}
