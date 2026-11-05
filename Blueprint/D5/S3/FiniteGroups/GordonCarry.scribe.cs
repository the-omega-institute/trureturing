using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class GordonCarryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GordonCarry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/gordon1961sequences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd radix predecessor carries retain the whole bounded digit tuple.", H("Reversible mixed-radix carries"), Blocks(
            Describe.Lean(
                DescribeId.Create("gordon-gordoncarry-carry-injective"),
                DeclarationHandle.Create(Owner + "carry_injective"), H("Recovering the first nonzero digit"),
                StatementSource.FromAuthor(Disp(CarryInjective())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Each radix is odd and greater than one. Box is the nested product of its cyclic residue groups, with the least significant digit first. The predecessor borrows recursively through zero digits. In the carry output, digits before the first nonzero input digit vanish, that digit becomes its negative double, and higher digits become their negative doubles minus one. Inverting doubling recovers every digit. Empty lists and repeated radices are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordoncarry-carry-eq-zero"),
                DeclarationHandle.Create(Owner + "carry_eq_zero"), H("Complete borrow and the zero fiber"),
                StatementSource.FromAuthor(Disp(CarryZero())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A zero input borrows through every coordinate and produces zero. Injectivity proves the converse, including the empty tuple. This distinguishes an internal multiple of the odd radix product from any nonzero residue in the even-edge inventory."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordoncarry-rank-complement"),
                DeclarationHandle.Create(Owner + "rank_complement"), H("Digit complement reverses rank"),
                StatementSource.FromAuthor(Disp(Complement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Rank is the bounded mixed-radix integer, not a group homomorphism. Coordinatewise complement sends rank r to the product of the radices minus one minus r. This is the arithmetic step that separates opposite-parity prefixes."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordoncarry-pred-residue"),
                DeclarationHandle.Create(Owner + "pred_residue"), H("Predecessor agrees with modular subtraction"),
                StatementSource.FromAuthor(Disp(Predecessor())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Residue reduces a natural index modulo the product and decodes its bounded digits. For every positive index, digit predecessor agrees with index subtraction by one. At a multiple of the product this is the full wrap to the maximal tuple."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Digits(Formula body) => All("ds", Call("List", F.Id("OddRadix")), body);
    private static Formula CarryInjective() => Digits(Call("Injective", Call("carry", F.Id("ds"))));
    private static Formula CarryZero() {
        var ds = F.Id("ds"); var x = F.Id("x");
        return Digits(All("x", Call("Box", ds), Iff(Eq(Call("carry", ds, x), D(0)), Eq(x, D(0)))));
    }
    private static Formula Complement() {
        var ds = F.Id("ds"); var x = F.Id("x");
        return Digits(All("x", Call("Box", ds), Eq(Add(Add(Call("rank", ds, x),
            Call("rank", ds, Sub(Seq(Minus, x), Call("ones", ds)))), D(1)), Call("volume", ds))));
    }
    private static Formula Predecessor() {
        var ds = F.Id("ds"); var n = F.Id("n");
        return Digits(All("n", Nat(), Imp(Lt(D(0), n), Eq(Call("pred", ds, Call("residue", ds, n)),
            Call("residue", ds, Sub(n, D(1)))))));
    }

}
