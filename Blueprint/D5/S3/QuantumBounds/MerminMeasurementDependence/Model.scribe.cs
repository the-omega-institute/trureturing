using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/Model.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/alai2026staircase");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: Model",
        H("Model"),
        Blocks(
            Node("boolSign", Disp(All("b", F.Id("Bool"), Eqn(Call("boolSign" , F.Id("b")), IfF(F.Id("b"), new Formula.Negate(D(1)), D(1))))), "Boolean encoding of ±1.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Setting", Disp(All("n", NatF(), Eqn(Call("Setting" , F.Id("n")), SubtypeF("x", Arrow(Call("Fin" , F.Id("n")), F.Id("Bool")), Eqn(Call("NatMod" , Call("hammingDist" , F.Id("x"), Call("const" , Call("Fin" , F.Id("n")), F.Id("false"))), D(2)), D(0)))))), "Section II, PDF page 1: “The Mermin settings are strings s ∈ {X,Y}^n with an even number of Y's; there are 2^{n−1} of them.” Each setting occurs once.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Strategy", Disp(All("n", NatF(), Eqn(Call("Strategy" , F.Id("n")), Arrow(Call("Fin" , F.Id("n")), Call("Prod" , F.Id("Bool"), F.Id("Bool")))))), "Section II, PDF page 1: “A local deterministic model assigns each hidden state λ pre-set answers (a_i, b_i) ∈ {±1}² per party—4^n deterministic strategies—and, for each settings string s, a probability density ρ_s(λ).”", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("target", Disp(All("n", NatF(), All("x", SettingF(F.Id("n")), Eqn(Call("target" , F.Id("x")), Call("boolSign" , Call("decide" , Eqn(Call("NatMod" , Call("NatDiv" , Call("hammingDist" , Call("val" , F.Id("x")), Call("const" , Call("Fin" , F.Id("n")), F.Id("false"))), D(2)), D(2)), D(1)))))))), "Section II, PDF page 1: “Quantum mechanics predicts with certainty” E(s)=+1 when #Y(s)≡0 (mod 4), and E(s)=−1 when #Y(s)≡2 (mod 4), “with every proper-subset correlator vanishing.” The two-case displayed source equation appears verbatim in the Library note.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("responseBit", Disp(All("n", NatF(), All("lambda", StrategyF(F.Id("n")), All("x", SettingF(F.Id("n")), All("i", Call("Fin" , F.Id("n")), Eqn(Call("responseBit" , F.Id("lambda"), F.Id("x"), F.Id("i")), IfF(Call("apply" , Call("val" , F.Id("x")), F.Id("i")), Call("snd" , Call("apply" , F.Id("lambda"), F.Id("i"))), Call("fst" , Call("apply" , F.Id("lambda"), F.Id("i")))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("response", Disp(All("n", NatF(), All("lambda", StrategyF(F.Id("n")), All("x", SettingF(F.Id("n")), All("I", Call("Finset" , Call("Fin" , F.Id("n"))), Eqn(Call("response" , F.Id("lambda"), F.Id("x"), F.Id("I")), ProductF("i", Call("Fin" , F.Id("n")), F.Id("I"), Call("boolSign" , Call("responseBit" , F.Id("lambda"), F.Id("x"), F.Id("i")))))))))), "A subset correlator is the product of the selected deterministic outcomes.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsDensity", Disp(All("n", NatF(), All("rho", RhoF(F.Id("n")), IffF(Call("IsDensity" , F.Id("rho")), AndF(All("x", SettingF(F.Id("n")), All("lambda", StrategyF(F.Id("n")), LeqF(D(0), Call("apply" , F.Id("rho"), F.Id("x"), F.Id("lambda"))))), All("x", SettingF(F.Id("n")), Eqn(SumF("lambda", StrategyF(F.Id("n")), Call("apply" , F.Id("rho"), F.Id("x"), F.Id("lambda"))), D(1)))))))), "The probability density at each setting is nonnegative and normalized.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("correlator", Disp(All("n", NatF(), All("rho", RhoF(F.Id("n")), All("x", SettingF(F.Id("n")), All("I", Call("Finset" , Call("Fin" , F.Id("n"))), Eqn(Call("correlator" , F.Id("rho"), F.Id("x"), F.Id("I")), SumF("lambda", StrategyF(F.Id("n")), MulF(Call("apply" , F.Id("rho"), F.Id("x"), F.Id("lambda")), Call("response" , F.Id("lambda"), F.Id("x"), F.Id("I")))))))))), "Defining expression.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Faithful", Disp(All("n", NatF(), All("rho", RhoF(F.Id("n")), IffF(Call("Faithful" , F.Id("rho")), AndF(Call("IsDensity" , F.Id("rho")), AndF(All("x", SettingF(F.Id("n")), Eqn(Call("correlator" , F.Id("rho"), F.Id("x"), F.Id("univ")), Call("target" , F.Id("x")))), All("x", SettingF(F.Id("n")), All("I", Call("Finset" , Call("Fin" , F.Id("n"))), Imp(Call("Nonempty" , F.Id("I")), Imp(Ne(F.Id("I"), F.Id("univ")), Eqn(Call("correlator" , F.Id("rho"), F.Id("x"), F.Id("I")), D(0)))))))))))), "Section II, PDF page 1: “A model is faithful if it reproduces every full correlator E(s) and every vanishing proper-subset correlator.” Nonempty proper subsets may contain arbitrary mixtures of X and Y measurements.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("M", Disp(All("n", NatF(), All("rho", RhoF(F.Id("n")), Eqn(Call("M" , F.Id("rho")), Call("sSup" , Call("range" , Lam("xy", Call("Prod" , SettingF(F.Id("n")), SettingF(F.Id("n"))), SumF("lambda", StrategyF(F.Id("n")), AbsF(SubF(Call("apply" , F.Id("rho"), Call("fst" , F.Id("xy")), F.Id("lambda")), Call("apply" , F.Id("rho"), Call("snd" , F.Id("xy")), F.Id("lambda")))))))))))), "Section II, PDF page 1 defines M := max_{s,s′} ∑_λ |ρ_s(λ) − ρ_s′(λ)|. The range is finite and nonempty for n ≥ 3, so sSup equals its maximum.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("F", Disp(All("n", NatF(), All("rho", RhoF(F.Id("n")), Eqn(Call("F" , F.Id("rho")), Fr(Call("M" , F.Id("rho")), D(2)))))), "Section II, PDF page 1: “and the fraction of measurement independence surrendered is F := M/2 ∈ [0,1].” F is the surrendered fraction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ratio", Disp(All("n", NatF(), Eqn(Call("ratio" , F.Id("n")), Pow(D(2), Call("NatDiv" , Call("NatSub" , F.Id("n"), D(1)), D(2)))))), "Section IX, PDF page 4 defines R(n) := 2^{⌊(n−1)/2⌋}.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("floorValue", Disp(All("n", NatF(), Eqn(Call("floorValue" , F.Id("n")), Fr(CastF(Call("ratio" , F.Id("n"))), MulF(D(2), AddF(CastF(Call("ratio" , F.Id("n"))), D(1))))))), "The conjectured value R/(2(R+1)), as a real number.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-model-" + name.ToLowerInvariant().Replace("_", "-")),
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
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula SubF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumF(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula ProductF(string name, Formula type, Formula set, Formula body) =>
        Seq(Prod, Underscore, Grp(F.Id(name), Colon, type, Sp, InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula SubtypeF(string name, Formula type, Formula cond) =>
        Seq(OpenBrace, F.Id(name), Colon, type, Sp, Mid, Sp, cond, CloseBrace);
    private static Formula AbsF(Formula x) => Seq(Lvert, Parenthesized(x), Rvert);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula RhoF(Formula n) => Arrow(SettingF(n), Arrow(StrategyF(n), RealF()));
    private static Formula CastF(Formula x) => Call("RealCast", x);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Call("If", cond, yes, no);
}
