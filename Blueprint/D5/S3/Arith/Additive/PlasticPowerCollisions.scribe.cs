using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticPowerCollisionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/PlasticPowerCollisions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer plastic powers have four collision templates, disjoint unordered-pair fibers, and an exact finite-subset sumset identity.",
        H("Collisions of integer plastic powers"),
        Blocks(
            Paragraph(Text("Throughout, r is a real number with r > 1 and r³ = r + 1. Every exponent is an integer. "
                + "For a finite integer set E, A(r,E) denotes its image under e ↦ rᵉ. A(r,E) + A(r,E) is the actual pointwise real sumset. "
                + "Pairs are sorted, with repeated summands permitted. For d,a,b, N(E,d,a,b) is the cardinality of {t ∈ E : t+a ∈ E, t+b ∈ E, t+d ∈ E}. "
                + "These are abbreviations for the explicit Finset.image and Finset.filter expressions in Lean, without an abstract sumset model.")),
            Node("difference_eq_one_iff", "The integer difference equation", Difference(),
                "If the lower exponent is negative, the upper exponent lies strictly between zero and three. "
                + "Otherwise dividing by the lower power bounds the positive exponent gap by two. "
                + "The identities r−1 = r⁻⁴ and r²−1 = r⁻¹ give all four solutions. "
                + "This elementary argument is the source proof's intermediate step; negative exponents remain in its domain.", false),
            Node("normalized_collision_iff", "All four normalized templates", Normalized(),
                "Dividing by the largest inner power shows that d−b is one or two, since the resulting power is below two and r³ > 2. "
                + "The difference classification then gives exactly (4,2,3), (6,3,5), (7,5,5), and (9,5,8). "
                + "The third template retains the diagonal pair. Bérczes Theorems 2.2 and 2.3 attest the collision classification.", true),
            Node("sorted_collision_iff", "Translated sorted pairs", Sorted(),
                "For sorted pairs with i < k, an equality of sums forces l < j. Dividing by rⁱ converts to the normalized equation. "
                + "The converse multiplies that equation by the same nonzero power, preserving all integer translates.", true),
            Node("sum_fiber_card_le_two", "Actual sum fibers have size at most two", Fiber(),
                "Pairs with the same first exponent and the same sum are equal. For three distinct representations, order the first exponents. "
                + "The middle pair would need both an outer gap in {4,6,7,9} and an inner gap in {0,1,2,3}. "
                + "These are disjoint, so three representations cannot occur.", false),
            Node("sumset_card_eq_reduced_pairs", "One representative for every real sum", Reduced(),
                "Write O(E,p) for the disjunction p₂=p₁+4 with p₁+2,p₁+3 in E; p₂=p₁+6 with p₁+3,p₁+5 in E; "
                + "p₂=p₁+7 with p₁+5 in E; or p₂=p₁+9 with p₁+5,p₁+8 in E. "
                + "Each excluded outer pair has an inner partner in E with the same actual real sum. That partner cannot itself be outer, "
                + "since this would give three representations. The sum map on the remaining pairs is both injective and onto the actual sumset.", false),
            Node("sumset_card_add_template_counts", "Exact counting for arbitrary finite exponent sets", Counting(),
                "The excluded pairs form the disjoint union of the four translated templates; their outer gaps distinguish the four parts. "
                + "Each part is in bijection with its starting exponents. All sorted pairs consist of the strictly ordered pairs and the diagonal, "
                + "so their total is choose(|E|+1,2). The additive identity proves that subtracting the four counts cannot truncate. "
                + "The three-point template uses N(E,7,5,5), where the repeated membership condition is redundant.", false),
            Node("nested_family_sum_card", "The exact native nested-family sumset", Nested(),
                "Let E(n) = {0,3} ∪ [5,n+2] over the integers, and B(r,n) = A(r,E(n)). "
                + "For n ≥ 7, this exponent set has n elements. The starting exponents for the four templates are respectively "
                + "{3} ∪ [5,n−2], {0,3} ∪ [5,n−4], {0} together with 3 when n ≥ 8 and [5,n−5], "
                + "and {0} together with 3 when n ≥ 10 and [5,n−7]. Counting these sets and applying the exact finite-subset identity "
                + "gives every positive-part and indicator term in source Theorem 2.1. "
                + "Natural subtraction represents the positive parts; the additive equality proves no truncation in the displayed source subtraction.", false),
            Paragraph(Text("This supplies the collision and arbitrary-finite-subset counting bridge used in the proof of source Theorem 2.1. "
                + "The source theorem additionally requires its product equality, strict nesting, "
                + "and the comparison with the golden-ratio power set. Those additional claims are not consequences asserted by this document."))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool attested) =>
        Describe.Lean(DescribeId.Create("plastic-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            attested ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula V(string x) => F.Id(x);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Named(string x) => Seq(Operatorname, Grp(V(x)));
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Named(x), [..a]);
    private static Formula All(string x, Formula t, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(x), Sp, Colon, Sp, t)), Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Or,Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Iff,Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Pow(Formula a) => new Formula.Power(V("r"),a);
    private static Formula Z() => Seq(Mathbb,Grp(V("Z")));
    private static Formula R() => Seq(Mathbb,Grp(V("R")));
    private static Formula PairType() => Seq(Z(),Sp,Times,Sp,Z());
    private static Formula Part(string x, byte i) => new Formula.Subscript(V(x),D(i));
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula SetOf(string x, Formula t, Formula body) =>
        Seq(OpenBrace,V(x),Sp,Colon,Sp,t,Sp,Mid,Sp,body,CloseBrace);
    private static Formula Root(Formula body) => All("r",R(),Imp(Lt(D(1),V("r")),
        Imp(Eq(new Formula.Power(V("r"),D(3)),Add(V("r"),D(1))),body)));
    private static Formula WithE(Formula body) => Root(All("E",Call("Finset",Z()),body));
    private static Formula SumPair(string p) => Add(Pow(Part(p,1)),Pow(Part(p,2)));
    private static Formula InPairs(string p) => Rel(V(p),FormulaRelationOperator.MemberOf,
        Seq(V("E"),Sp,Times,Sp,V("E")));
    private static Formula SumCard() => Card(Add(Call("A",V("r"),V("E")),Call("A",V("r"),V("E"))));
    private static Formula Cases(Formula[] a) => a.Aggregate(Or);

    private static Formula Difference()
    {
        Formula Sol(byte u, byte v, bool negative) => And(Eq(V("u"),D(u)),
            Eq(V("v"),negative ? Seq(Minus,D(v)) : D(v)));
        var body = IffF(Eq(Sub(Pow(V("u")),Pow(V("v"))),D(1)),
            Cases([Sol(1,4,true),Sol(2,1,true),Sol(3,1,false),Sol(5,4,false)]));
        return Disp(Root(All("u",Z(),All("v",Z(),body))));
    }
    private static Formula Normalized()
    {
        Formula Sol(byte d, byte a, byte b) => And(Eq(V("d"),D(d)),And(Eq(V("a"),D(a)),Eq(V("b"),D(b))));
        var eq = Eq(Add(D(1),Pow(V("d"))),Add(Pow(V("a")),Pow(V("b"))));
        var body = IffF(eq,Cases([Sol(4,2,3),Sol(6,3,5),Sol(7,5,5),Sol(9,5,8)]));
        body = Imp(Le(D(1),V("a")),Imp(Le(V("a"),V("b")),Imp(Lt(V("b"),V("d")),body)));
        body = All("d",Z(),All("a",Z(),All("b",Z(),body)));
        return Disp(Root(body));
    }
    private static Formula Sorted()
    {
        Formula Sol(byte d, byte a, byte b) => And(Eq(V("j"),Add(V("i"),D(d))),
            And(Eq(V("k"),Add(V("i"),D(a))),Eq(V("l"),Add(V("i"),D(b)))));
        var eq = Eq(Add(Pow(V("i")),Pow(V("j"))),Add(Pow(V("k")),Pow(V("l"))));
        var body = IffF(eq,Cases([Sol(4,2,3),Sol(6,3,5),Sol(7,5,5),Sol(9,5,8)]));
        body = Imp(Le(V("i"),V("j")),Imp(Le(V("k"),V("l")),Imp(Lt(V("i"),V("k")),body)));
        body = All("i",Z(),All("j",Z(),All("k",Z(),All("l",Z(),body))));
        return Disp(Root(body));
    }
    private static Formula Fiber() => Disp(WithE(All("x",R(),Le(Card(SetOf("p",PairType(),
        And(InPairs("p"),And(Le(Part("p",1),Part("p",2)),Eq(SumPair("p"),V("x")))))),D(2)))));
    private static Formula Reduced() => Disp(WithE(Eq(SumCard(),Card(SetOf("p",PairType(),
        And(InPairs("p"),And(Le(Part("p",1),Part("p",2)),Seq(Neg,Sp,Call("O",V("E"),V("p"))))))))));
    private static Formula Nested()
    {
        var n = V("n");
        Formula Positive(byte x) => new Formula.Subscript(Par(Sub(n,D(x))),Plus);
        Formula Indicator(byte x) => new Formula.Subscript(D(1),Le(D(x),n));
        var c = Add(Add(Add(Add(Add(Sub(n,D(1)),Positive(8)),Positive(9)),
            new Formula.Subscript(Par(Sub(n,D(1,1))),Plus)),Indicator(8)),
            new Formula.Subscript(D(1),Le(D(1,0),n)));
        var b = Call("B",V("r"),n);
        return Disp(Root(All("n",Seq(Mathbb,Grp(V("N"))),Imp(Le(D(7),n),
            Eq(Add(Card(Add(b,b)),c),new Formula.Fraction(
                new Formula.Binary(n,FormulaBinaryOperator.Multiply,Par(Add(n,D(1)))),D(2)))))));
    }
    private static Formula Counting()
    {
        Formula N(byte d, byte a, byte b) => Call("N",V("E"),D(d),D(a),D(b));
        var total = Add(Add(Add(Add(SumCard(),N(4,2,3)),N(6,3,5)),N(7,5,5)),N(9,5,8));
        return Disp(WithE(Eq(total,Call("choose",Add(Card(V("E")),D(1)),D(2)))));
    }
}
