using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class GordonProductDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GordonProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/gordon1961sequences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic carry construction gives an orthogonal path for the regular translation action.", H("Gordon interleaving and directed differences"), Blocks(
            Describe.Lean(
                DescribeId.Create("gordon-gordonproduct-vertex-injective"),
                DeclarationHandle.Create(Owner + "vertex_injective"), H("All prefix vertices are distinct"),
                StatementSource.FromAuthor(Disp(PrefixClaim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Write D for the odd radix product, L=hD and N=2L. The vertex function is restricted here to indices zero through N minus one. Its even vertices are minus F(j); its odd vertices are F(j) plus the tuple of ones, for j less than L. Same-parity equality gives congruences modulo 2h and D. Opposite-parity equality forces complementary digits and N to divide u+v+1, which lies strictly between zero and N."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordonproduct-difference-injective"),
                DeclarationHandle.Create(Owner + "difference_injective"), H("The two difference inventories"),
                StatementSource.FromAuthor(Disp(DifferenceClaim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The difference function is restricted here to indices zero through N minus two. Odd-first-coordinate labels are 2F(j)+C for j less than L. Even labels are minus F(j) minus F(j-1) minus C for positive j less than L. The reversible carry recovers j modulo D, while the first coordinate recovers it modulo h. Parity separates the families. Chinese remaindering is used between h and D; no pairwise coprimality of odd radices is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordonproduct-product-sequencing"),
                DeclarationHandle.Create(Owner + "product_sequencing"), H("Every original nonzero label exactly once"),
                StatementSource.FromAuthor(Disp(WordClaim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The word has N minus one labels. They are distinct and nonzero, so cardinality gives every nonzero group element once. Its prefix sums telescope to the N distinct vertices, including the empty and full prefix. For q=2 raised to a positive exponent take h=q/2; coprimality with D follows from oddness. This includes q=2, no odd factors, and repeated odd factors. Translations by group elements form a regular action. Consecutive vertices use each nonzero translation label once, so the vertex path and the directed-label inventory are simultaneous properties."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gordon-gordonproduct-word-endpoint"),
                DeclarationHandle.Create(Owner + "word_endpoint"), H("The terminal prefix"),
                StatementSource.FromAuthor(Disp(Endpoint())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The final odd digits are all radix minus one and cancel the tuple of ones. Since D is odd, the first coordinate is h modulo 2h. The endpoint is therefore (h,0), and differs from the empty prefix for positive h."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Star, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
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
    private static Formula Product(Formula body, bool positive = false) {
        var h = F.Id("h"); var ds = F.Id("ds");
        var hypothesis = Call("Coprime", h, Call("volume", ds));
        if (positive) hypothesis = And(Lt(D(0), h), hypothesis);
        return All("h", Nat(), All("ds", Call("List", F.Id("OddRadix")), Imp(hypothesis, body)));
    }
    private static Formula Word() => Call("word", F.Id("h"), F.Id("ds"));
    private static Formula ProductGroup() => Call("Product", Call("ZMod", Mul(D(2), F.Id("h"))), Call("Box", F.Id("ds")));
    private static Formula PrefixClaim() => Product(Call("Injective", Call("restrict", Call("vertex", F.Id("h"), F.Id("ds")),
        Call("Fin", Mul(D(2), Mul(F.Id("h"), Call("volume", F.Id("ds"))))))));
    private static Formula DifferenceClaim() => Product(Call("Injective", Call("restrict", Call("difference", F.Id("h"), F.Id("ds")),
        Call("Fin", Sub(Mul(D(2), Mul(F.Id("h"), Call("volume", F.Id("ds")))), D(1))))));
    private static Formula WordClaim() => Product(And(Inventory(ProductGroup(), Word()), PrefixInjective(Word())), true);
    private static Formula Endpoint() => All("h", Nat(), All("ds", Call("List", F.Id("OddRadix")),
        Imp(Lt(D(0), F.Id("h")), Eq(Call("sum", Word()), Call("pair", F.Id("h"), D(0))))));

}
