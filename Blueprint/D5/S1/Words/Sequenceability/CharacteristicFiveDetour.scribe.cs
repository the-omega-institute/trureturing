using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class CharacteristicFiveDetourDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Op(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Op(s), [.. xs]);
    private static Formula All(string s, Formula ty, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), ty, b);
    private static Formula Ex(string s, Formula ty, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), ty, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Inst(string s, params Formula[] xs) => Seq(OpenBracket, Call(s, xs), CloseBracket, Sp);
    private static Formula Lam(string s, Formula ty, Formula b) => Seq(Open, V(s), Colon, ty, Mapsto, Sp, b, Close);
    private static Formula Nat => Call("Nat");
    private static Formula Group => Seq(Call("ZMod", D(5)), Sp, Times, Sp, V("K"));
    private static Formula Vert(Formula n) => Call("v", n);
    private static Formula Edge(Formula n) => Sub(Vert(Add(n, D(1))), Vert(n));
    private static Formula Outside => Seq(OpenBrace, V("z"), Colon, Group, Mid,
        Ne(Call("fst", V("z")), D(0)), CloseBrace);
    private static Formula Prefix(Formula n) => Seq(Sum, Underscore,
        Grp(V("i"), Lt, n), Edge(V("i")));
    private static Formula Formula()
    {
        Formula m = V("M");
        Formula domain = Call("Fin", Add(m, D(1)));
        Formula interval = All("a", Nat, All("b", Nat,
            Imp(And(new Formula.Relation(V("a"), FormulaRelationOperator.LessThan, V("b")),
                    new Formula.Relation(V("b"), FormulaRelationOperator.LessThanOrEqual, m)),
                Ne(Seq(Sum, Underscore, Grp(V("a"), Le, Sp, V("i"), Lt, V("b")), Edge(V("i"))), D(0)))));
        Formula body = And(Eqn(Vert(D(0)), Pair(D(0), D(0))),
            And(Eqn(Vert(m), Pair(D(0), V("u"))),
            And(Call("Injective", Lam("n", domain, Vert(Call("val", V("n"))))),
            And(Call("BijOn", V("v"), Call("Ioo", D(0), m), Outside),
            And(Call("BijOn", Lam("n", Nat, Edge(V("n"))), Call("Iio", m),
                Seq(Outside, Cup, OpenBrace, Pair(D(0), V("u")), CloseBrace)),
            And(Call("Injective", Lam("k", domain, Prefix(Call("val", V("k"))))),
            And(interval, Eqn(Prefix(m), Pair(D(0), V("u"))))))))));
        body = Ex("v", Seq(Nat, To, Sp, Group), body);
        body = Seq(Op("let"), Sp, m, Eq, Add(Seq(D(4), Cdot, Call("card", V("K"))), D(1)), Semi, body);
        body = All("u", V("K"), Imp(Ne(V("u"), D(0)), body));
        return Disp(All("K", Call("Type"), Seq(Inst("Field", V("K")), Inst("Finite", V("K")),
            Inst("CharP", V("K"), D(5)), body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three cuts join the two row-lift cycles into an exact relative path.",
        H("Characteristic-five relative paths"), Blocks(
            Paragraph(Text("Let K be any finite field of characteristic five and let u be nonzero. "
                + "Write B for the vectors (a,h) in ZMod(5) times K with a nonzero. "
                + "All directed labels are differences of actual vertices with coefficient one.")),
            Describe.Lean(DescribeId.Create("characteristic-five-relative-path"),
                DeclarationHandle.Create("D5/S1/Words/Sequenceability/CharacteristicFiveDetour.exists_characteristic_five_relative_path"),
                H("A path with exact vertices, labels and bounded sums"),
                StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The path has M+1=4*card(K)+2 distinct vertices and M=4*card(K)+1 edges. "
                        + "Its endpoints are (0,0) and (0,u). BijOn on the open interval of indices means that "
                        + "the interior contains every vector of B exactly once. BijOn for the edge differences "
                        + "means that their inventory is exactly B together with the single label (0,u), each once. "
                        + "Every prefix through the full endpoint is distinct, including the empty prefix. "
                        + "Every nonempty interval, including the whole path, has nonzero sum, and the total is (0,u). "
                        + "Values of v beyond index M are unrestricted.")),
                    Paragraph(Text("Use the row lift with center 4u and quotient columns (1,2,4,3). "
                        + "Its carrier phases 0,1,2,3 denote those four column values, respectively. "
                        + "The removed edges are (1,2u) to (2,3u), (2,u) to (4,4u), and (4,3u) to (3,2u). "
                        + "Their labels are (1,u), (2,3u), and (4,4u). The middle removed edge lies on the "
                        + "small row-lift cycle; the first and third lie on the other cycle.")),
                    Paragraph(Text("On the carrier (Fin(4) times K) plus Fin(2), extend the lift P by fixing "
                        + "s and t. Set h=(1,3u), j=(2,4u), k=(3,2u) in the old carrier, and take "
                        + "Q=swap(h,s)*swap(h,t)*swap(j,k)*P, with the rightmost action first. "
                        + "Swapping the two attachments merges the disjoint old cycles. The next two swaps "
                        + "insert the fixed points t and s. A first-return argument also applies to singleton "
                        + "cycles and leaves unrelated ambient cycles alone. Thus Q is one cycle on the full carrier.")),
                    Paragraph(Text("Read the orbit of Q from s through t, and omit its closing edge t to s. "
                        + "The four new joins have labels (2,3u), (0,u), (1,u), and (4,4u). "
                        + "The first, third and fourth replace the three removed old labels once each. "
                        + "An explicit permutation of the three cut tails and s proves the punctured difference "
                        + "bijection. The closing label (0,-u) is excluded. Orbit injectivity and its exact period "
                        + "identify t as the last vertex. Telescoping then gives the prefix, interval and total clauses.")),
                    Paragraph(Text("This relative path can replace an edge of an existing path in the zero column: "
                        + "translate it to the chosen edge's source, so its last vertex is the old target. "
                        + "The interior stays outside the zero column, and the replacement adds every outside label. "
                        + "A prime seed, the branch for primes at least seven, insertion in a complete induction, "
                        + "and transport to arbitrary original coordinates require their own proofs."))),
                DescribeRole.Theorem))));
}
