using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyOddProductDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyOddProduct.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even R-star base times any odd finite abelian group retains its prescribed zero-row triple.", H("HeadleyOddProduct"), Blocks(
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-difference-spec"),
                DeclarationHandle.Create(Owner + "difference_spec"), H("Actual successor and difference permutations"),
                StatementSource.FromAuthor(Disp(Difference())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S is the ordinary row lift after a source three-cycle on the a,zero,b columns for each internally selected positive row. D is the old difference permutation after the inverse source three-cycle. The additive relation a+c=b proves that these are the actual labels S(v)-v in original product coordinates. Composition of equivalences supplies both inverse laws for S and D; no label inventory is a premise. The two inverse-pair paths and their six labels are attributed to Section 4 of the earlier native Headley construction and the accepted odd-row proof, not claimed as a new literature result."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-box-first-return"),
                DeclarationHandle.Create(Owner + "box_first_return"), H("The complete first positive return"),
                StatementSource.FromAuthor(Disp(FirstReturn())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The gadget uses two steps at row zero and three steps on any other row. The ordinary tail uses M-3 steps, with its first lift T1 and the even remaining M-4 negations. Their ordered composite returns (a,h) to (a,pred(h)). No intermediate gadget vertex has first coordinate a; bounded injectivity of the base orbit excludes a from every intermediate ordinary column. The proof includes closure and the M=4 tail. This is an actual power statement about the defined successor, rather than an assumed row-return certificate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-nonzero-cycle"),
                DeclarationHandle.Create(Owner + "nonzero_cycle"), H("All row blocks form the entire nonzero orbit"),
                StatementSource.FromAuthor(Disp(Cycle())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each inverse pair has paths (a,h),(0,-h),(0,h),(c,-h) and (a,-h),(b,h),(b,-h),(c,h); the zero row retains (a,0),(b,0),(c,0). The actual ordinary tail starts with T1 and then uses an even number M-4 of negations. Its complete return is predecessor. Every exceptional vertex is on one of these paths. The original base cycle enumerates every other column, and each intermediate row map is a permutation, so every ordinary fiber is reached. The predecessor cycle connects all a-rows. The nonzero restriction reuses HeadleyExtension.bijOn_complement at the fixed origin. This proves one cycle on the entire nonzero product, with no additional component or unaccounted seam. The M=4, trivial-row and row-order-three cases remain in the same construction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-exists-rstar-product"),
                DeclarationHandle.Create(Owner + "exists_rstar_product"), H("The full arbitrary odd-factor theorem with the exact triple"),
                StatementSource.FromAuthor(Disp(Product())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input is an RStar on X, which includes Even(Nat.card X), and Odd(Nat.card H), for arbitrary finite additive commutative groups. The output is an RStar on X×H with a=(r.a,0), b=(r.b,0), c=(r.c,0). The proof supplies actual successor and difference permutations, fixing the origin, the entire nonzero cycle, every triple field and even cardinality. The odd factor is obtained by the original unconditional Gordon decomposition. HeadleyExtension.transportCycle supplies the entire transported RCycle, preserving the fixed origin, the full nonzero cycle and every coefficient-one difference; the added RStar fields retain the literal zero-row triple and even cardinality. There is no generator, supplied decomposition, orthomorphism, inventory or cycle-certificate premise. The intended consumer is the odd quotient factor in the Headley extension program. The full Headley induction, full uniform finite-field route and original arbitrary-subset/same-M/original-coordinate/coefficient-one parent remain open; this theorem does not settle them. The faithful original-telescope four-slot Reg attempt remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21042; no validated Reg or observational-dependence claim is supplied."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Group(string name, Formula body) => All(name, F.Id("Type"),
        Seq(Instance("AddCommGroup", F.Id(name)), Instance("Finite", F.Id(name)), body));
    private static Formula Base(Formula body) => Group("X", All("r", Call("RStar", F.Id("X")), body));
    private static Formula Rows(Formula body) => Base(All("ds", Call("List", F.Id("OddRadix")), body));
    private static Formula Box() => Call("Box", F.Id("ds"));
    private static Formula Pair(Formula x, Formula h) => Call("pair", x, h);
    private static Formula VertexType() => Call("Prod", F.Id("X"), Box());
    private static Formula Succ() => Call("successor", F.Id("r"), F.Id("ds"));
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Power(Formula n, Formula x) => Apply(Call("pow", Succ(), n), x);
    private static Formula Field(string name, Formula r) => Call(name, r);
    private static Formula Difference() => Rows(All("v", VertexType(),
        Eq(Apply(Call("difference", F.Id("r"), F.Id("ds")), F.Id("v")),
            Sub(Apply(Succ(), F.Id("v")), F.Id("v")))));
    private static Formula FirstReturn()
    {
        var h = F.Id("h"); var i = F.Id("i"); var a = Field("a", F.Id("r"));
        var len = Call("ite", Eq(h, D(0)), Sub(Call("card", F.Id("X")), D(1)), Call("card", F.Id("X")));
        return Rows(Seq(Instance("Fintype", F.Id("X")), All("h", Box(), And(
            Eq(Power(len, Pair(a, h)), Pair(a, Call("predecessor", F.Id("ds"), h))),
            All("i", F.Id("Nat"), Imp(And(Lt(D(0), i), Lt(i, len)),
                Ne(Call("fst", Power(i, Pair(a, h))), a)))))));
    }
    private static Formula Cycle() => Rows(Seq(Instance("Fintype", F.Id("X")),
        Call("IsCycleOn", Succ(), Call("nonzero", VertexType()))));
    private static Formula Product()
    {
        var x = F.Id("X"); var h = F.Id("H"); var r = F.Id("r"); var o = F.Id("rOut");
        Formula Label(string name) => Eq(Field(name, o), Pair(Field(name, r), D(0)));
        return Group("X", Group("H", All("r", Call("RStar", x),
            Imp(Call("Odd", Call("card", h)), Ex("rOut", Call("RStar", Call("Prod", x, h)),
                And(Label("a"), And(Label("b"), Label("c"))))))));
    }
}
