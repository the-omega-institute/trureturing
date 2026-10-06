using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class AlaiStaircaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/alai2026staircase");

    private const string SourceConjecture = "Section IX, Conjecture 1 (Staircase), PDF page 4: “With R(n) := 2^{⌊(n−1)/2⌋} the Mermin violation ratio and s(n) := (R+1)/(2R) the classical satisfiability, F_min(n) = R/(2(R+1)) = 1/(4 s(n)), F_min·s = 1/4.” The Library note quotes the literal source TeX, including the displayed equation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: AlaiStaircase",
        H("AlaiStaircase"),
        Blocks(
            Node("classicalS", Disp(All("n", NatF(), Eqn(Call("classicalS" , F.Id("n")), Fr(AddF(CastF(Call("ratio" , F.Id("n"))), D(1)), MulF(D(2), CastF(Call("ratio" , F.Id("n")))))))), "Section IX, PDF page 4 defines s(n) := (R+1)/(2R).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("attainableF", Disp(All("n", NatF(), Eqn(Call("attainableF" , F.Id("n")), SubtypeF("z", RealF(), Ex("rho", RhoF(F.Id("n")), AndF(Call("Faithful" , F.Id("rho")), Eqn(Call("F" , F.Id("rho")), F.Id("z")))))))), "Section II, PDF page 1: “The floors reported below are minima of F over all faithful models for the stated finite setting sets; richer scenarios containing them can only raise the values.” This is the set of attainable real F values, rather than a subtype carrier.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Fmin", Disp(All("n", NatF(), Eqn(Call("Fmin" , F.Id("n")), Call("sInf" , Call("attainableF" , F.Id("n")))))), "The infimum of attainable values. result proves it is attained and therefore is the minimum specified by the source.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Disp(IffF(F.Id("claim"), All("n", NatF(), Imp(LeqF(D(3), F.Id("n")), AndF(Eqn(Call("Fmin" , F.Id("n")), Fr(CastF(Call("ratio" , F.Id("n"))), MulF(D(2), AddF(CastF(Call("ratio" , F.Id("n"))), D(1))))), AndF(Eqn(Call("Fmin" , F.Id("n")), Fr(D(1), MulF(D(4), Call("classicalS" , F.Id("n"))))), AndF(Eqn(MulF(Call("Fmin" , F.Id("n")), Call("classicalS" , F.Id("n"))), Fr(D(1), D(4))), AndF(Ex("rho", RhoF(F.Id("n")), AndF(Call("Faithful" , F.Id("rho")), Eqn(Call("F" , F.Id("rho")), Call("Fmin" , F.Id("n"))))), All("rho", RhoF(F.Id("n")), Imp(Call("Faithful" , F.Id("rho")), LeqF(Call("Fmin" , F.Id("n")), Call("F" , F.Id("rho"))))))))))))), SourceConjecture + " The quantifier n ≥ 3 comes from the scenario in Section II, PDF page 1. Fin n labels parties, ratio is R(n), classicalS is s(n), and Fmin is the infimum of F over faithful models. The assertion includes attainment by a faithful model and the lower bound for every faithful model.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", Disp(F.Id("claim")), "The odd and even faithful constructions attain the lower bound. The attained infimum is the minimum; real algebra gives its classical-satisfiability form and product identity.", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alai-2026-ghz-mermin-staircase"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("alai-alaistaircase-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role, resolution);

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
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MulF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SubtypeF(string name, Formula type, Formula cond) =>
        Seq(OpenBrace, F.Id(name), Colon, type, Sp, Mid, Sp, cond, CloseBrace);
    private static Formula NatF() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula SettingF(Formula n) => Call("Setting", n);
    private static Formula StrategyF(Formula n) => Call("Strategy", n);
    private static Formula RhoF(Formula n) => Arrow(SettingF(n), Arrow(StrategyF(n), RealF()));
    private static Formula CastF(Formula x) => Call("RealCast", x);

}
