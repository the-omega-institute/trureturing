using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinHTransversalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinHTransversals.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ghafari2026transversals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cap and bulk columns and symbols of the H-family profiles have no repetitions within either region.",
        H("Coordinates of the H-family transversals"),
        Blocks(
            Node("bulk-column-injective", "Bulk column injectivity",
                "bulk_column_injective", BulkInjectiveFormula("column"),
                "For every permitted order and profile, the four unbounded bulk classes use different column residues on distinct bulk rows, including the empty bulk at order thirty-six."),
            Node("bulk-symbol-injective", "Bulk symbol injectivity",
                "bulk_symbol_injective", BulkInjectiveFormula("symbol"),
                "The four bulk symbol progressions likewise have no repeated residue, after the possible wrap at the order is resolved uniformly."),
            Node("cap-column-injective", "Cap column injectivity",
                "cap_column_injective", CapInjectiveFormula("column"),
                "The thirty-six cap column pairs are distinct after modular reduction for every permitted order. The four affine complement blocks remain disjoint even near the smallest order."),
            Node("cap-symbol-injective", "Cap symbol injectivity",
                "cap_symbol_injective", CapInjectiveFormula("symbol"),
                "The thirty-six cap symbol pairs are likewise distinct after modular reduction, using their exact four-block affine complement certificate.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("latin-h-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula BulkInjectiveFormula(string coordinate)
    {
        var k = F.Id("k"); var j = F.Id("j");
        var p = F.Id("p"); var q = F.Id("q");
        var domain = Call("Prod", Call("Fin", Sub(k, D(9))), Call("Fin", D(4)));
        Formula Value(Formula index) => Call(coordinate, k, j,
            Call("bulkRow", k, Call("fst", index), Call("snd", index)));
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)), All("p", domain, All("q", domain,
                Imp(Eq(Value(p), Value(q)), Eq(p, q))))))));
    }

    private static Formula CapInjectiveFormula(string coordinate)
    {
        var k = F.Id("k"); var j = F.Id("j");
        var i = F.Id("i"); var l = F.Id("l");
        var domain = Call("Fin", D(3, 6));
        Formula Value(Formula index) => Call(coordinate, k, j,
            Call("capRow", k, index));
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)), All("i", domain, All("l", domain,
                Imp(Eq(Value(i), Value(l)), Eq(i, l))))))));
    }
}
