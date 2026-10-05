using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class FiberLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/alai2026staircase");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: FiberLift",
        H("FiberLift"),
        Blocks(
            Node("AlphaFiber", Disp(All("n", NatF(), All("P", BitF(), Eqn(Call("AlphaFiber" , F.Id("n"), F.Id("P")), SubtypeF("alpha", CubeF(F.Id("n")), Eqn(SumF("i", Call("Fin" , F.Id("n")), Call("apply" , F.Id("alpha"), F.Id("i"))), F.Id("P"))))))), "The parity fiber consists of all output vectors with the prescribed total parity. Under the complementary binary sign encoding, parity_conditioned_moments gives zero expectation for every nonempty proper subset.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tableOfAlphaGamma", Disp(All("n", NatF(), All("alpha", CubeF(F.Id("n")), All("gamma", CubeF(F.Id("n")), Eqn(Call("tableOfAlphaGamma" , F.Id("alpha"), F.Id("gamma")), Lam("i", Call("Fin" , F.Id("n")), PairF(Call("decide", Eqn(Call("apply" , F.Id("alpha"), F.Id("i")), D(1))), Call("decide", Eqn(AddF(Call("apply" , F.Id("alpha"), F.Id("i")), Call("apply" , F.Id("gamma"), F.Id("i"))), D(1)))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fiberEquiv", Disp(All("d", NatF(), All("P", BitF(), Eqn(Call("fiberEquiv" , F.Id("d"), F.Id("P")), Call("Equiv" , Lam("alpha", Call("AlphaFiber" , AddF(F.Id("d"), D(1)), F.Id("P")), Lam("i", Call("Fin" , F.Id("d")), Call("apply" , Call("val" , F.Id("alpha")), Call("castSucc" , F.Id("i"))))), Lam("x", CubeF(F.Id("d")), Call("Subtype" , Call("snoc" , F.Id("x"), AddF(F.Id("P"), SumF("i", Call("Fin" , F.Id("d")), Call("apply" , F.Id("x"), F.Id("i")))))))))))), "A parity vector is determined by its first d coordinates; the final coordinate is P plus their sum. Both inverse laws are verified.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fiberMixture", Disp(All("d", NatF(), All("C", F.Id("Type"), BracketF(Call("Fintype" , F.Id("C")), All("P", Arrow(F.Id("C"), BitF()), All("p", Arrow(F.Id("C"), RealF()), All("z", Call("Sigma" , Lam("c", F.Id("C"), Call("AlphaFiber" , AddF(F.Id("d"), D(1)), Call("apply" , F.Id("P"), F.Id("c"))))), Eqn(Call("fiberMixture" , F.Id("P"), F.Id("p"), F.Id("z")), Fr(Call("apply" , F.Id("p"), Call("fst" , F.Id("z"))), Pow(D(2), F.Id("d"))))))))))), "Uniformly distribute each class weight over its parity fiber.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("liftClassTable", Disp(All("d", NatF(), All("C", F.Id("Type"), All("P", Arrow(F.Id("C"), BitF()), All("gamma", Arrow(F.Id("C"), CubeF(AddF(F.Id("d"), D(1)))), All("z", Call("Sigma" , Lam("c", F.Id("C"), Call("AlphaFiber" , AddF(F.Id("d"), D(1)), Call("apply" , F.Id("P"), F.Id("c"))))), Eqn(Call("liftClassTable" , F.Id("P"), F.Id("gamma"), F.Id("z")), Call("tableOfAlphaGamma" , Call("val" , Call("snd" , F.Id("z"))), Call("apply" , F.Id("gamma"), Call("fst" , F.Id("z"))))))))))), "The deterministic table associated with a class and an output parity vector.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("liftedDensity", Disp(All("d", NatF(), All("C", F.Id("Type"), BracketF(Call("Fintype" , F.Id("C")), All("P", Arrow(F.Id("C"), BitF()), All("gamma", Arrow(F.Id("C"), CubeF(AddF(F.Id("d"), D(1)))), All("p", Arrow(F.Id("C"), RealF()), Eqn(Call("liftedDensity" , F.Id("P"), F.Id("gamma"), F.Id("p")), Call("channelOutput" , Lam("z", Call("Sigma" , Lam("c", F.Id("C"), Call("AlphaFiber" , AddF(F.Id("d"), D(1)), Call("apply" , F.Id("P"), F.Id("c"))))), Lam("lambda", StrategyF(AddF(F.Id("d"), D(1))), IfF(Eqn(Call("liftClassTable" , F.Id("P"), F.Id("gamma"), F.Id("z")), F.Id("lambda")), D(1), D(0)))), Call("fiberMixture" , F.Id("P"), F.Id("p"))))))))))), "Push class weights through ClassicalDPI.channelOutput with the deterministic indicator channel. Contributions from classes mapping to the same table are summed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("classResponse", Disp(All("d", NatF(), All("C", F.Id("Type"), All("P", Arrow(F.Id("C"), BitF()), All("gamma", Arrow(F.Id("C"), CubeF(AddF(F.Id("d"), D(1)))), All("x", SettingF(AddF(F.Id("d"), D(1))), All("c", F.Id("C"), Eqn(Call("classResponse" , F.Id("P"), F.Id("gamma"), F.Id("x"), F.Id("c")), MulF(Call("bitSign" , Call("apply" , F.Id("P"), F.Id("c"))), Call("bitSign" , SumF("i", Call("Fin" , AddF(F.Id("d"), D(1))), MulF(Call("apply" , F.Id("gamma"), F.Id("c"), F.Id("i")), Call("ZModCast" , Call("toNat" , Call("apply" , Call("val" , F.Id("x")), F.Id("i")))))))))))))))), "The class full response in parity and relative-output coordinates.", DescribeRole.Definition, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-fiberlift-" + name.ToLowerInvariant().Replace("_", "-")),
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
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumF(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula PairF(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula SubtypeF(string name, Formula type, Formula cond) =>
        Seq(OpenBrace, F.Id(name), Colon, type, Sp, Mid, Sp, cond, CloseBrace);
    private static Formula BracketF(Formula value, Formula body) =>
        Seq(OpenBracket, value, CloseBracket, Sp, body);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula BitF() => Call("ZMod", D(2));
    private static Formula CubeF(Formula n) => Arrow(Call("Fin", n), BitF());
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Call("If", cond, yes, no);
}
