using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class OverlapBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/alai2026staircase");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: OverlapBound",
        H("OverlapBound"),
        Blocks(
            Node("pointwise_min_sum", Disp(All("S", F.Id("Type"), BracketF(Call("Fintype" , F.Id("S")), BracketF(Call("DecidableEq" , F.Id("S")), All("r", Arrow(F.Id("S"), RealF()), All("m", NatF(), Imp(All("x", F.Id("S"), LeqF(D(0), Call("apply" , F.Id("r"), F.Id("x")))), Imp(LeqF(Call("card" , Call("filter" , F.Id("univ"), Lam("x", F.Id("S"), Ne(Call("apply" , F.Id("r"), F.Id("x")), D(0))))), F.Id("m")), LeqF(SumF("x", F.Id("S"), SumF("y", F.Id("S"), IfF(Eqn(F.Id("x"), F.Id("y")), D(0), Call("min" , Call("apply" , F.Id("r"), F.Id("x")), Call("apply" , F.Id("r"), F.Id("y")))))), MulF(SubF(CastF(F.Id("m")), D(1)), SumF("x", F.Id("S"), Call("apply" , F.Id("r"), F.Id("x"))))))))))))), "Restrict to the support and erase the diagonal. Each inner overlap sum is bounded by (support size−1) times the row mass; summation gives the cap estimate.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("finite_overlap_lower_bound", Disp(All("S", F.Id("Type"), All("A", F.Id("Type"), BracketF(Call("Fintype" , F.Id("S")), BracketF(Call("Fintype" , F.Id("A")), BracketF(Call("DecidableEq" , F.Id("S")), All("rho", Arrow(F.Id("S"), Arrow(F.Id("A"), RealF())), All("m", NatF(), Imp(LeqF(D(2), Call("card" , F.Id("S"))), Imp(All("x", F.Id("S"), All("a", F.Id("A"), LeqF(D(0), Call("apply" , F.Id("rho"), F.Id("x"), F.Id("a"))))), Imp(All("x", F.Id("S"), Eqn(SumF("a", F.Id("A"), Call("apply" , F.Id("rho"), F.Id("x"), F.Id("a"))), D(1))), Imp(All("a", F.Id("A"), LeqF(Call("card" , Call("filter" , F.Id("univ"), Lam("x", F.Id("S"), Ne(Call("apply" , F.Id("rho"), F.Id("x"), F.Id("a")), D(0))))), F.Id("m"))), Ex("x", F.Id("S"), Ex("y", F.Id("S"), AndF(Ne(F.Id("x"), F.Id("y")), LeqF(Fr(SubF(CastF(Call("card" , F.Id("S"))), CastF(F.Id("m"))), SubF(CastF(Call("card" , F.Id("S"))), D(1))), Call("totalVariation" , Call("apply" , F.Id("rho"), F.Id("x")), Call("apply" , F.Id("rho"), F.Id("y"))))))))))))))))))), "Sum all off-diagonal density overlaps and use pointwise_min_sum. At least one pair has overlap at most the average; its total variation is at least (number of settings−cap)/(number of settings−1).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("literal_index_lower", Disp(All("n", NatF(), All("S", F.Id("Type"), BracketF(Call("Fintype" , F.Id("S")), All("embed", Arrow(F.Id("S"), SettingF(F.Id("n"))), All("m", NatF(), Imp(LeqF(D(2), Call("card" , F.Id("S"))), Imp(All("lambda", StrategyF(F.Id("n")), LeqF(Call("card" , Call("filter" , F.Id("univ"), Lam("x", F.Id("S"), Eqn(Call("response" , F.Id("lambda"), Call("apply" , F.Id("embed"), F.Id("x")), F.Id("univ")), Call("target" , Call("apply" , F.Id("embed"), F.Id("x"))))))), F.Id("m"))), All("rho", RhoF(F.Id("n")), Imp(Call("Faithful" , F.Id("rho")), LeqF(Fr(SubF(CastF(Call("card" , F.Id("S"))), CastF(F.Id("m"))), SubF(CastF(Call("card" , F.Id("S"))), D(1))), Call("F" , F.Id("rho"))))))))))))), "Section VIII, Theorem 5, PDF page 4: the general satisfaction-cap lower bound. Extreme targets force every violating table to have zero density. The pairwise lower bound therefore applies to any chosen finite index set of settings.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-overlapbound-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula SubF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumF(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula BracketF(Formula value, Formula body) =>
        Seq(OpenBracket, value, CloseBracket, Sp, body);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula RhoF(Formula n) => Arrow(SettingF(n), Arrow(StrategyF(n), RealF()));
    private static Formula CastF(Formula x) => Call("RealCast", x);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Call("If", cond, yes, no);
}
