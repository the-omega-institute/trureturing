using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class OddConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: OddConstruction",
        H("OddConstruction"),
        Blocks(
            Node("odd_construction", Disp(All("k", NatF(), Imp(LeqF(D(1), F.Id("k")), Ex("rho", RhoF(AddF(MulF(D(2), F.Id("k")), D(1))), AndF(Call("Faithful" , F.Id("rho")), Eqn(Call("F" , F.Id("rho")), Call("floorValue" , AddF(MulF(D(2), F.Id("k")), D(1))))))))), "Construct mass on the positive rows of the flat-spectrum sign design and lift through parity fibers. The parity_conditioned_moments theorem gives cancellation of every nonempty proper-subset correlator in the lift. Its total variation is bounded by the class-level variation via the frozen data-processing theorem; the universal lower bound gives equality.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("oddGamma", Disp(All("k", NatF(), All("a", CubeF(MulF(D(2), F.Id("k"))), Eqn(Call("oddGamma" , F.Id("k"), F.Id("a")), Call("snoc" , F.Id("a"), D(0)))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("oddRow", Disp(All("k", NatF(), All("x", SettingF(AddF(MulF(D(2), F.Id("k")), D(1))), All("a", CubeF(MulF(D(2), F.Id("k"))), Eqn(Call("oddRow" , F.Id("k"), F.Id("x"), F.Id("a")), Call("spectralRow" , F.Id("k"), Call("freeSetting" , F.Id("x")), F.Id("a"))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-oddconstruction-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula BitF() => Call("ZMod", D(2));
    private static Formula CubeF(Formula n) => Arrow(Call("Fin", n), BitF());
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula RhoF(Formula n) => Arrow(SettingF(n), Arrow(StrategyF(n), RealF()));

}
