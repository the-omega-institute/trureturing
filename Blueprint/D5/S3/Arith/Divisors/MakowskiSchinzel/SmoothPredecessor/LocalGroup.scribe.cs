using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorLocalGroupDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite subgroups and certified prefixes", H("Finite subgroups and certified prefixes"),
        Blocks(Node("finite_subgroup_bound", "Rank domination of an arbitrary finite subset",
            Finite(), "Let qs be a nondecreasing list of natural numbers. Sorting any " +
                "finite subset F of its values gives a list that dominates the equally " +
                "long prefix of qs coordinatewise. The factors (q-1)/q increase on positive q; " +
                "at q=0 the factor is zero, which also preserves the comparison. Thus the " +
                "lowerProduct of the sorted F is at least that prefix product and its rounded fixed " +
                "product divided by scale. The exact (q-1)/q factors retain zero at q=0. " +
                "Repetitions in qs are allowed. Ordering and membership " +
                "are needed: the prefix of [3,2] at length one has product 2/3, exceeding " +
                "the product 1/2 over F={2}; the list [3] gives the same failure without membership."),
            Node("table_group_prefix_bound", "Every finite subgroup inherits a checked prefix",
                PrefixBound(), "For arbitrary T, tail list tl, tail tuple t and final state z, assume " +
                "groupValues(i,T) " +
                "is nondecreasing and stepTable(tl,T,initialState)=some(z). Require " +
                "the selected group to pass its terminal check only if card(F) equals its full length. " +
                "At index i with " +
                "oddPrimes[i]=some(p) and tl[i]=some(t), no order between different groups is needed. For " +
                "every finite subset F of one such subsequence, the certificate supplies " +
                "a prefix check at count card(F), with fixed product L. Rank domination " +
                "makes L/scale a lower bound for the exact lowerProduct of sorted F. For positive q, the factor " +
                "(q-1)/q equals 1-1/q. The terminal " +
                "check covers the case in which F has the full group size. No entry " +
                "validity or counting condition is required. The ordered input is " +
                "needed for rank domination, the run checks proper prefixes, the " +
                "final test checks the full prefix, and the two lookups identify " +
                "the prime and the exact tail constant used by that group."))));

    private static Formula Finite()
    {
        var qs = V("l");
        var subset = All("q", Nat(), Imp(Mem(V("q"), V("s")), Mem(V("q"), qs)));
        var value = Call("lowerProduct", Call("take", Call("card", V("s")), qs));
        return All("l", Call("List", Nat()), All("s", Call("Finset", Nat()),
            Imp(Call("PairwiseLe", qs), Imp(subset, Le(value, Call("lowerProduct", Call("sort", V("s"))))))));
    }

    private static Formula PrefixBound()
    {
        var table = V("T"); var tails = V("tl"); var final = V("z");
        var group = Call("groupValues", V("i"), table);
        var result = And(
            Eq(Call("prefixOk", V("p"), Call("card", V("s")),
                Call("fixedProduct", Call("scale"),
                    Call("take", Call("card", V("s")), group)),
                V("t")), Call("true")),
            Le(Div(Call("fixedProduct", Call("scale"),
                Call("take", Call("card", V("s")), group)), Call("scale")), Call("lowerProduct", Call("sort", V("s")))));
        var last = All("j", Nat(), All("L", Nat(),
            Imp(Eq(Call("getElemOption", final, V("i")), Call("some", Call("Pair", V("j"), V("L")))),
                Eq(Call("prefixOk", V("p"), V("j"), V("L"), V("t")), Call("true")))));
        result = Imp(Imp(Eq(Call("card", V("s")), Call("length", group)), last), result);
        result = Imp(All("q", Nat(), Imp(Mem(V("q"), V("s")), Mem(V("q"), group))), result);
        result = All("s", Call("Finset", Nat()), result);
        result = Imp(Eq(Call("getElemOption", tails, V("i")), Call("some", V("t"))), result);
        result = Imp(Eq(Call("getElemOption", Call("oddPrimes"), V("i")),
            Call("some", V("p"))), result);
        result = Imp(Call("PairwiseLe", group), result);
        result = All("p", Nat(), result);
        result = All("i", Nat(), result);
        result = All("t", Call("Pair", Nat(), Call("Pair", Nat(), Nat())), result);
        result = Imp(Eq(Call("stepTable", tails, table, Call("initialState")),
            Call("some", final)), result);
        return All("T", Call("List", Nat()),
            All("tl", Call("List", Call("Pair", Nat(), Call("Pair", Nat(), Nat()))),
                All("z", Call("List", Call("Pair", Nat(), Nat())), result)));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("smooth-predecessor-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
}
