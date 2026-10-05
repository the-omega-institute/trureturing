using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class CoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: Coordinates",
        H("Coordinates"),
        Blocks(
            Node("bitSign", Disp(All("z", BitF(), Eqn(Call("bitSign" , F.Id("z")), Call("boolSign" , Call("decide", Eqn(F.Id("z"), D(1))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("tableParity", Disp(All("n", NatF(), All("lambda", StrategyF(F.Id("n")), Eqn(Call("tableParity" , F.Id("lambda")), SumF("i", Call("Fin" , F.Id("n")), Call("ZModCast" , Call("toNat" , Call("fst" , Call("apply" , F.Id("lambda"), F.Id("i")))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("tableGamma", Disp(All("n", NatF(), All("lambda", StrategyF(F.Id("n")), All("i", Call("Fin" , F.Id("n")), Eqn(Call("tableGamma" , F.Id("lambda"), F.Id("i")), AddF(Call("ZModCast" , Call("toNat" , Call("fst" , Call("apply" , F.Id("lambda"), F.Id("i"))))), Call("ZModCast" , Call("toNat" , Call("snd" , Call("apply" , F.Id("lambda"), F.Id("i"))))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("evenExtension", Disp(All("d", NatF(), All("x", CubeF(F.Id("d")), Eqn(Call("evenExtension" , F.Id("x")), Call("snoc" , Lam("i", Call("Fin" , F.Id("d")), Call("decide", Eqn(Call("apply" , F.Id("x"), F.Id("i")), D(1)))), Call("decide", Eqn(SumF("i", Call("Fin" , F.Id("d")), Call("apply" , F.Id("x"), F.Id("i"))), D(1)))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("evenSetting", Disp(All("d", NatF(), All("x", CubeF(F.Id("d")), Eqn(Call("evenSetting" , F.Id("x")), Call("Subtype" , Call("evenExtension" , F.Id("x"))))))), "The defining underlying string is evenExtension x; its parity proof is supplied in Lean.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lastAdjustedFrequency", Disp(All("d", NatF(), All("lambda", StrategyF(AddF(F.Id("d"), D(1))), All("i", Call("Fin" , F.Id("d")), Eqn(Call("lastAdjustedFrequency" , F.Id("lambda"), F.Id("i")), AddF(Call("tableGamma" , F.Id("lambda"), Call("castSucc" , F.Id("i"))), Call("tableGamma" , F.Id("lambda"), Call("last" , F.Id("d"))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("freeSetting", Disp(All("d", NatF(), All("x", SettingF(AddF(F.Id("d"), D(1))), Eqn(Call("freeSetting" , F.Id("x")), Lam("i", Call("Fin" , F.Id("d")), Call("ZModCast" , Call("toNat" , Call("apply" , Call("val" , F.Id("x")), Call("castSucc" , F.Id("i")))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("settingEquiv", Disp(All("d", NatF(), Eqn(Call("settingEquiv" , F.Id("d")), Call("Equiv" , F.Id("freeSetting"), F.Id("evenSetting"))))), "The two maps are freeSetting and evenSetting at dimension d. The Lean definition verifies both inverse laws.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("addX", Disp(All("d", NatF(), All("x", SettingF(F.Id("d")), Eqn(Call("addX" , F.Id("x")), Call("Subtype" , Call("snoc" , Call("val" , F.Id("x")), F.Id("false"))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("flipSetting", Disp(All("n", NatF(), All("hn", Call("Even" , F.Id("n")), All("x", SettingF(F.Id("n")), Eqn(Call("flipSetting" , F.Id("hn"), F.Id("x")), Call("Subtype" , Lam("i", Call("Fin" , F.Id("n")), Call("not" , Call("apply" , Call("val" , F.Id("x")), F.Id("i")))))))))), "Complement every setting bit. Even n ensures the complement remains an even-Y setting.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("evenRepresentative", Disp(All("k", NatF(), All("x", SettingF(AddF(MulF(D(2), F.Id("k")), D(2))), Eqn(Call("evenRepresentative" , F.Id("k"), F.Id("x")), IfF(Call("apply" , Call("val" , F.Id("x")), Call("last" , AddF(MulF(D(2), F.Id("k")), D(1)))), Call("flipSetting" , Call("proofOf" , Call("Even" , AddF(MulF(D(2), F.Id("k")), D(2)))), F.Id("x")), F.Id("x")))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("evenReduced", Disp(All("k", NatF(), All("x", SettingF(AddF(MulF(D(2), F.Id("k")), D(2))), Eqn(Call("evenReduced" , F.Id("k"), F.Id("x")), Call("Subtype" , Lam("i", Call("Fin" , AddF(MulF(D(2), F.Id("k")), D(1))), Call("apply" , Call("val" , Call("evenRepresentative" , F.Id("k"), F.Id("x"))), Call("castSucc" , F.Id("i"))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("evenFactor", Disp(All("k", NatF(), All("x", SettingF(AddF(MulF(D(2), F.Id("k")), D(2))), Eqn(Call("evenFactor" , F.Id("k"), F.Id("x")), IfF(Call("apply" , Call("val" , F.Id("x")), Call("last" , AddF(MulF(D(2), F.Id("k")), D(1)))), Call("bitSign" , Call("ZModCast" , AddF(F.Id("k"), D(1)))), D(1)))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-coordinates-" + name.ToLowerInvariant().Replace("_", "-")),
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
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumF(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BitF() => Call("ZMod", D(2));
    private static Formula CubeF(Formula n) => Arrow(Call("Fin", n), BitF());
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Call("If", cond, yes, no);
}
