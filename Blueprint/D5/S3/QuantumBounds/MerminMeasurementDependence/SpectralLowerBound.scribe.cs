using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class SpectralLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: SpectralLowerBound",
        H("SpectralLowerBound"),
        Blocks(
            Node("spectralRow", Disp(All("k", NatF(), All("x", CubeF(MulF(D(2), F.Id("k"))), All("a", CubeF(MulF(D(2), F.Id("k"))), Eqn(Call("spectralRow" , F.Id("k"), F.Id("x"), F.Id("a")), MulF(MulF(Call("bitSign" , Call("qFree" , F.Id("x"))), Call("bitSign" , Call("walshParity" , F.Id("k"), F.Id("a")))), Call("character" , F.Id("a"), F.Id("x")))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("capValue", Disp(All("k", NatF(), Eqn(Call("capValue" , F.Id("k")), Call("NatDiv" , AddF(Pow(D(2), MulF(D(2), F.Id("k"))), Pow(D(2), F.Id("k"))), D(2))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("staircase_lower", Disp(All("n", NatF(), Imp(LeqF(D(3), F.Id("n")), All("rho", RhoF(F.Id("n")), Imp(Call("Faithful" , F.Id("rho")), LeqF(Call("floorValue" , F.Id("n")), Call("F" , F.Id("rho")))))))), "For odd n use all even settings. For even n embed the odd-size subset by appending X. Affine agreement bounds its satisfaction cap, and the finite overlap estimate forces a distant pair of densities.", DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-spectrallowerbound-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula BitF() => Call("ZMod", D(2));
    private static Formula CubeF(Formula n) => Arrow(Call("Fin", n), BitF());
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula RhoF(Formula n) => Arrow(SettingF(n), Arrow(StrategyF(n), RealF()));

}
