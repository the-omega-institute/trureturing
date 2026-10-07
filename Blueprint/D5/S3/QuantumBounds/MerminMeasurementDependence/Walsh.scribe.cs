using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class WalshDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: Walsh",
        H("Walsh"),
        Blocks(
            Node("qFree", Disp(All("d", NatF(), All("x", CubeF(F.Id("d")), Eqn(Call("qFree" , F.Id("x")), AddF(Call("ZModCast" , Call("choose" , Call("hammingDist" , Lam("i", Call("Fin" , F.Id("d")), Call("decide", Eqn(Call("apply" , F.Id("x"), F.Id("i")), D(1)))), Call("const" , Call("Fin" , F.Id("d")), F.Id("false"))), D(2))), SumF("i", Call("Fin" , F.Id("d")), Call("apply" , F.Id("x"), F.Id("i")))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("walsh", Disp(All("d", NatF(), All("a", CubeF(F.Id("d")), Eqn(Call("walsh" , F.Id("a")), SumF("x", CubeF(F.Id("d")), Call("bitSign" , AddF(Call("qFree" , F.Id("x")), SumF("i", Call("Fin" , F.Id("d")), MulF(Call("apply" , F.Id("a"), F.Id("i")), Call("apply" , F.Id("x"), F.Id("i"))))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("qFree_polar", Disp(All("d", NatF(), All("x", CubeF(F.Id("d")), All("y", CubeF(F.Id("d")), Eqn(AddF(AddF(Call("qFree" , AddF(F.Id("x"), F.Id("y"))), Call("qFree" , F.Id("x"))), Call("qFree" , F.Id("y"))), AddF(SumF("i", Call("Fin" , F.Id("d")), MulF(Call("apply" , F.Id("x"), F.Id("i")), Call("apply" , F.Id("y"), F.Id("i")))), MulF(SumF("i", Call("Fin" , F.Id("d")), Call("apply" , F.Id("x"), F.Id("i"))), SumF("i", Call("Fin" , F.Id("d")), Call("apply" , F.Id("y"), F.Id("i")))))))))), "Induction over the number of coordinates proves the polar identity. Arithmetic occurs in ZMod 2.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("character", Disp(All("d", NatF(), All("a", CubeF(F.Id("d")), All("x", CubeF(F.Id("d")), Eqn(Call("character" , F.Id("a"), F.Id("x")), Call("bitSign" , SumF("i", Call("Fin" , F.Id("d")), MulF(Call("apply" , F.Id("a"), F.Id("i")), Call("apply" , F.Id("x"), F.Id("i")))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("qFree_walsh_square", Disp(All("k", NatF(), All("a", CubeF(MulF(D(2), F.Id("k"))), Eqn(Pow(Call("walsh" , F.Id("a")), D(2)), Pow(D(2), MulF(D(2), F.Id("k"))))))), "Translate one variable in the squared Walsh sum. Character orthogonality annihilates every translation outside the radical; the polar radical is trivial in even dimension.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("walshParity", Disp(All("k", NatF(), All("a", CubeF(MulF(D(2), F.Id("k"))), Eqn(Call("walshParity" , F.Id("k"), F.Id("a")), IfF(new Formula.Relation(Call("walsh" , F.Id("a")), FormulaRelationOperator.LessThan, D(0)), D(1), D(0)))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("affine_agreement_bound", Disp(All("k", NatF(), All("b", BitF(), All("a", CubeF(MulF(D(2), F.Id("k"))), LeqF(CastF(Call("card" , Call("filter" , F.Id("univ"), Lam("x", CubeF(MulF(D(2), F.Id("k"))), Eqn(Call("qFree" , F.Id("x")), AddF(F.Id("b"), SumF("i", Call("Fin" , MulF(D(2), F.Id("k"))), MulF(Call("apply" , F.Id("a"), F.Id("i")), Call("apply" , F.Id("x"), F.Id("i")))))))))), Fr(AddF(Pow(D(2), MulF(D(2), F.Id("k"))), Pow(D(2), F.Id("k"))), D(2))))))), "Flat Walsh magnitude bounds the number of agreements with every affine function.", DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-walsh-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumF(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BitF() => Call("ZMod", D(2));
    private static Formula CubeF(Formula n) => Arrow(Call("Fin", n), BitF());
    private static Formula CastF(Formula x) => Call("RealCast", x);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Call("If", cond, yes, no);
}
