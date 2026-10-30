using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class GordonFullSetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GordonFullSet.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/gordon1961sequences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gordon sequencing preserves every original label and coefficient one.", H("Full-set sequencing in finite abelian groups"), Blocks(
            Describe.Lean(
                DescribeId.Create("gordon-gordonfullset-sum-ne-zero-iff-unique-involution"),
                DeclarationHandle.Create(Owner + "sum_ne_zero_iff_unique_involution"), H("The total and the unique involution"),
                StatementSource.FromAuthor(Disp(TorsionStatement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Nonzero total gives one positive even prime-power factor and an odd digit box. Its unique nonzero element killed by doubling is the terminal prefix (h,0); the box has injective doubling. Conversely, after removing the unique nonzero involution, negation pairs every remaining nonzero term with its negative. The total therefore equals that involution. The sequencing theorem consumes this equivalence before selecting its prime-power presentation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordonfullset-exists-full-set-sequencing"),
                DeclarationHandle.Create(Owner + "exists_full_set_sequencing"), H("The complete finite-abelian theorem"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Total means the sum of all elements of the finite additive abelian group. A nonzero total forces exactly one nontrivial even prime-power factor in the finite-abelian decomposition. Odd factors have zero total because doubling is invertible; two even factors make every coordinate total vanish by the product cardinality multiplicities. Trivial exponents are removed and the remaining odd prime powers form the digit box. The inverse additive equivalence transports the complete product word to the original group. Each original nonzero element occurs exactly once with coefficient one. Every prefix, including zero and the whole word, is distinct; subtraction of two prefixes gives the nonzero sum of every nonempty interval. This is Gordon's published full-set result. The arbitrary-subset problem remains unresolved by this construction, since deleting labels changes prefix sums."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Typ() => Seq(F.Id("Type"), Star);
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Member(Formula x, Formula w) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, w);
    private static Formula Prefix(Formula w, Formula k) => Call("sum", Call("take", k, w));
    private static Formula PrefixInjective(Formula w) {
        var k = F.Id("k"); var l = F.Id("l"); var len = Call("length", w);
        return All("k", Nat(), All("l", Nat(), Imp(And(Le(k, len), Le(l, len)),
            Imp(Eq(Prefix(w, k), Prefix(w, l)), Eq(k, l)))));
    }
    private static Formula Inventory(Formula g, Formula w) {
        var x = F.Id("x");
        return And(Call("Nodup", w), All("x", g, Iff(Member(x, w), Ne(x, D(0)))));
    }
    private static Formula TorsionStatement() {
        var g = F.Id("G"); var t = F.Id("t"); var x = F.Id("x");
        var law = And(Ne(t, D(0)), Eq(Add(t, t), D(0)));
        var unique = All("x", g, Imp(And(Ne(x, D(0)), Eq(Add(x, x), D(0))), Eq(x, t)));
        return All("G", Typ(), Seq(Instance("AddCommGroup", g), Instance("Fintype", g),
            Iff(Ne(Call("total", g), D(0)), Exists("t", g, And(law, unique)))));
    }
    private static Formula Statement() {
        var g = F.Id("G"); var w = F.Id("w"); var i = F.Id("i"); var j = F.Id("j");
        var intervals = All("i", Nat(), All("j", Nat(), Imp(And(Lt(i, j), Le(j, Call("length", w))),
            Ne(Call("sum", Call("take", Sub(j, i), Call("drop", i, w))), D(0)))));
        return All("G", Typ(), Seq(Instance("AddCommGroup", g), Instance("Fintype", g),
            Imp(Ne(Call("total", g), D(0)), Exists("w", Call("List", g),
                And(Inventory(g, w), And(PrefixInjective(w), intervals))))));
    }

}
