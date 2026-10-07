using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class LatinHLatinnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/LatinHLatinness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ghafari2026transversals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal H square is Latin for every integer parameter at least nine.",
        H("Latinness of the literal H family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latin-h-latinness"),
                DeclarationHandle.Create(Prefix + "literal_h_latinness"),
                H("The literal H square is Latin"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every integer K at least nine, put k equal to its natural representative and use the native order-four-k H square. Every fixed row and every fixed column is a bijection. The proof follows the priority delta table directly: residue equality is reduced to the zero, plus-one-modulus, or minus-one-modulus alternatives; the exceptional cap rows and columns, the parity-controlled bulk swaps, the K = 9 empty bulk, and the K = 10 first bulk block are all discharged in the same universal argument."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Int() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Int"));

    private static Formula ResultFormula()
    {
        var k = Call("toNat", F.Id("K"));
        return Disp(All("K", Int(),
            Imp(Le(D(9), F.Id("K")),
                Call("IsLatin", Call("order", k), Call("square", k)))));
    }
}
