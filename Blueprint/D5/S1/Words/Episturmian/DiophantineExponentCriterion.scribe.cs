using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Episturmian;

internal sealed class DiophantineExponentCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Episturmian/DiophantineExponentCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/peltomaki2024episturmian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Episturmian words: DiophantineExponentCriterion.", H("DiophantineExponentCriterion"),
        Blocks(
            Node("result-0", "result", DeclarationHandle.Create(Prefix + "result"), Disp(ResultFormula()), "The alphabet is Fin d, letters are indexed from zero, and equality of Lang expresses equality of factor sets.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("peltomaki-2024-episturmian-diophantine-exponent"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, DeclarationHandle declaration, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolves = null) => Describe.Lean(
        DescribeId.Create(id), declaration, H(title), StatementSource.FromAuthor(formula), provenance,
        Narrative(title, prose), role, resolves);


    private static BlockSequence Narrative(string title, string prose) => title is "claim" or "result"
        ? Blocks(
            Paragraph(DefinitionDsl.Text("Let "), Math(Seq(Mathbf, Grp(F.Id("t")))),
                DefinitionDsl.Text(" be an aperiodic episturmian word. Then "),
                Math(Rel(App(F.Id("dio"), Seq(Mathbf, Grp(F.Id("t")))), FormulaRelationOperator.LessThan, Infty)),
                DefinitionDsl.Text(" if and only if "), Math(Seq(Mathbf, Grp(F.Id("t")))),
                DefinitionDsl.Text(" has bounded partial quotients.")),
            Paragraph(DefinitionDsl.Text("Peltomäki, Conjecture 8.4, Section 8.")),
            Paragraph(DefinitionDsl.Text(prose)))
        : Blocks(Paragraph(DefinitionDsl.Text(prose)));

    private static Formula AperiodicityFormula() => Seq(Neg, Sp, Parenthesized(Ex("N", F.Id("Nat"), Ex("p", F.Id("Nat"), And(Rel(D(0), FormulaRelationOperator.LessThan, F.Id("p")), All("n", F.Id("Nat"), Imp(Rel(F.Id("N"), FormulaRelationOperator.LessThanOrEqual, F.Id("n")), Rel(App(F.Id("t"), Parenthesized(Seq(F.Id("n"), Plus, F.Id("p")))), FormulaRelationOperator.Equal, App(F.Id("t"), F.Id("n"))))))))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Arrow(Formula left, Formula right) => Parenthesized(new Formula.TypeArrow(Parenthesized(left), Parenthesized(right)));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Parenthesized(type), body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Parenthesized(type), body);

    private static Formula ResultFormula() =>
        All("d", F.Id("Nat"), All("Delta", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), All("t", Arrow(F.Id("Nat"), App(F.Id("Fin"), F.Id("d"))), Imp(Rel(App(F.Id("Lang"), F.Id("t")), FormulaRelationOperator.Equal, App(F.Id("Lang"), Parenthesized(App(F.Id("cDelta"), F.Id("Delta"))))), Imp(AperiodicityFormula(), Parenthesized(Iff(Rel(App(F.Id("dio"), F.Id("t")), FormulaRelationOperator.LessThan, Infty), App(F.Id("BoundedPQ"), F.Id("Delta")))))))));
}
