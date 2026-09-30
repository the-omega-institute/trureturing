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
        "The literal cap columns and the unbounded bulk rows of the H family obey their stated coordinate and source equations.",
        H("Coordinates of the H-family transversals"),
        Blocks(
            Node("bulk-source-increment", "Bulk source increments",
                "bulk_source_increment", BulkIncrementFormula(),
                "On a bulk row of class zero the selected column is even and the source increment is two. The other three selected bulk classes have increment zero: class two uses an odd column, while classes one and three do not satisfy either modified-row guard."),
            Node("head-source-increment", "Head source increments",
                "head_source_increment", HeadIncrementFormula(),
                "The standard representatives of the fifteen head cap columns satisfy the eight source guards in their stated priority order. The negative raw columns minus three and minus one reduce to the last two representatives."),
            Node("source-compatibility", "Source compatibility for every row",
                "source_compatibility", SourceCompatibilityFormula(),
                "The head rows, four bulk classes, and tail rows exhaust the square, including the empty-bulk case at k equal to nine. On every row the explicit symbol equals the actual source-square entry."),
            Node("cap-zero-one-residue", "Equality of the first two cap columns",
                "cap_zero_one_residue_eq_iff", CapResidueFormula(),
                "After reduction modulo the order, the first two profiles still have an equal cap column exactly in cap row eleven. A difference strictly within one modulus can be divisible by the modulus only when it is zero."),
            Node("column-zero-one", "Common columns of the first two profiles",
                "column_zero_one_eq_iff", ColumnEqualityFormula(),
                "Every bulk column differs by four, and the cap certificate isolates row eleven. This proves that the two full column functions agree at exactly that row for every permitted order."),
            Node("exact-common-entry", "Exact common entry",
                "exact_common_entry", ExactIntersectionFormula(),
                "The first two literal entry sets meet only at the source entry in row eleven. The third profile uses a different column there, so their triple intersection is empty."),
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
    private static Formula Bool() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula ForBulk(Formula body)
    {
        var k = F.Id("k");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)),
                All("t", Call("Fin", Sub(k, D(9))),
                    All("r", Call("Fin", D(4)), body))))));
    }

    private static Formula ForCapIndex(Formula body, byte capLength)
    {
        var k = F.Id("k");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)),
                All("i", Call("Fin", D((byte)(capLength / 10), (byte)(capLength % 10))), body)))));
    }

    private static Formula BulkIncrementFormula()
    {
        var k = F.Id("k"); var j = F.Id("j");
        var t = F.Id("t"); var r = F.Id("r");
        var a = Call("bulkRow", k, t, r);
        var increment = Call("delta", k, a, Call("column", k, j, a));
        return ForBulk(And(
            Imp(Eq(Call("val", r), D(0)), Eq(increment, D(2))),
            Imp(Ne(Call("val", r), D(0)), Eq(increment, D(0)))));
    }

    private static Formula HeadIncrementFormula()
    {
        var k = F.Id("k"); var j = F.Id("j"); var i = F.Id("i");
        var a = Call("headRow", k, i);
        return ForCapIndex(Eq(Call("delta", k, a, Call("column", k, j, a)),
            Call("capEpsilon", j, Call("extend", i))), 15);
    }

    private static Formula SourceCompatibilityFormula()
    {
        var k = F.Id("k"); var j = F.Id("j"); var a = F.Id("a");
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("j", Call("Fin", D(3)),
                All("a", Call("Fin", Call("order", k)),
                    Eq(Call("symbol", k, j, a),
                        Call("square", k, a, Call("column", k, j, a))))))));
    }

    private static Formula CapResidueFormula()
    {
        var k = F.Id("k"); var odd = F.Id("odd"); var i = F.Id("i");
        var p = Call("capAffine", D(0), odd, i);
        var q = Call("capAffine", D(1), odd, i);
        var x = Add(Mul(Call("fst", p), k), Call("snd", p));
        var y = Add(Mul(Call("fst", q), k), Call("snd", q));
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("odd", Bool(), All("i", Call("Fin", D(3, 6)),
                Iff(Eq(Call("residue", k, x), Call("residue", k, y)),
                    Eq(Call("val", i), D(1, 1))))))));
    }

    private static Formula ColumnEqualityFormula()
    {
        var k = F.Id("k"); var a = F.Id("a");
        var statement = Iff(Eq(Call("column", k, D(0), a),
                Call("column", k, D(1), a)), Eq(Call("val", a), D(1, 1)));
        return Disp(All("k", Nat(), Imp(Le(D(9), k),
            All("a", Call("Fin", Call("order", k)), statement))));
    }

    private static Formula ExactIntersectionFormula()
    {
        var k = F.Id("k");
        var t0 = Call("T", k, D(0));
        var t1 = Call("T", k, D(1));
        var t2 = Call("T", k, D(2));
        var common = Call("inter", t0, t1);
        return Disp(All("k", Nat(), Imp(Le(D(9), k), And(
            Eq(common, new Formula.SetLiteral([Call("d2", k)])),
            Eq(Call("inter", common, t2), new Formula.SetLiteral([]))))));
    }

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
