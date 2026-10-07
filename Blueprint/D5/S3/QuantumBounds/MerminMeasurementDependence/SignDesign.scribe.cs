using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.MerminMeasurementDependence;

internal sealed class SignDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminMeasurementDependence/SignDesign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful GHZ–Mermin measurement dependence: SignDesign",
        H("SignDesign"),
        Blocks(
            Node("designDensity", Disp(All("X", F.Id("Type"), All("C", F.Id("Type"), BracketF(Call("Fintype" , F.Id("C")), All("c", Arrow(F.Id("X"), Arrow(F.Id("C"), RealF())), All("R", RealF(), All("x", F.Id("X"), All("a", F.Id("C"), Eqn(Call("designDensity" , F.Id("c"), F.Id("R"), F.Id("x"), F.Id("a")), Fr(AddF(D(1), Call("apply" , F.Id("c"), F.Id("x"), F.Id("a"))), AddF(CastF(Call("card" , F.Id("C"))), F.Id("R")))))))))))), "The exact defining density is (1+c(x,a))/(card C+R). For sign-valued rows it vanishes on negative entries; normalization and variation bounds require the proved row-sum identities.", DescribeRole.Definition, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("alai-signdesign-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.")), Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula BracketF(Formula value, Formula body) =>
        Seq(OpenBracket, value, CloseBracket, Sp, body);
    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula CastF(Formula x) => Call("RealCast", x);

}
