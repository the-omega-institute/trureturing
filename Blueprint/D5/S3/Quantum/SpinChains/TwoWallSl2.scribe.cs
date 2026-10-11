using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TwoWallSl2Document : IScribeDocumentDefinition
{
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("K");
    private static Formula C => F.Id("c");
    private static Formula J => F.Id("j");
    private static Formula T => F.Id("t");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Coords => Call("Coordinates", A, B);
    private static Formula Sites => Call("Pos", A, B);
    private static Formula CM => Call("m", C);
    private static Formula CN => Call("n", C);
    private static Formula CP => Call("p", C);
    private static Formula CU => Call("u", C);
    private static Formula CV => Call("v", C);
    private static Formula JVal => Call("val", J);
    private static Formula Next => Add(JVal, D(1));
    private static Formula Enc(Formula c) => Call("encode", c);
    private static Formula Word(Formula x) => Call("word", x);
    private static Formula LitDelta(Formula c) => Call("delta", K, Word(Enc(c)));
    private static Formula MarkDelta(Formula c) => Call("markedDelta", K, Enc(c));
    private static Formula Op(string name) => Call(name, K, A, B);
    private static Formula Shift(bool marked, Formula t) =>
        Call(marked ? "markedTranslation" : "translation", K, t);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two binary arcs between two cyclic walls carry an sl2 action that descends to literal words and has the physical lowering operator.",
        H("The sl2 action on two-wall words"),
        Blocks(
            Paragraph(Text("Let K be a field of characteristic zero and let a,b be natural numbers. Use the literal counted words, marked cover, binary coordinates and maps Q,S,Jstar of TwoWallWords and TwoWallMarked. A coordinate c has entries p,m,n,u,v with m+n=a+b and ones(u)+ones(v)=b. True is letter two and false is letter one. Every finite sum below is over bonds, preserving transition multiplicities. Fin(m−1) is empty for m=0 or m=1; subtraction in these index bounds is natural subtraction. Binary positions have zero-based indices, so the coefficient associated with j is (j+1)(m−j−1).")),
            Node("leftMove", "Swapping an inner bond of the first arc", MoveDefinition(false), true,
                "Exchange entries j and j+1 of u. Keep p,m,n and v. The exchange preserves the number of true entries, so the filling certificate remains valid."),
            Node("rightMove", "Swapping an inner bond of the second arc", MoveDefinition(true), true,
                "Exchange entries j and j+1 of v and retain the first arc. Both operations also apply to unequal entries in either orientation."),
            Node("markedH", "The marked weight operator", MarkedDefinition("markedH"), true,
                "The sum of the existing rational bin weights acts diagonally on the marked delta basis. Each rational scalar is cast to K. These basis images determine the linear endomorphism."),
            Node("markedE", "The marked raising operator", MarkedDefinition("markedE"), true,
                "For each arc, sum the enabled 12 to 21 transitions with coefficient (j+1)(m−j−1). The distinguished wall remains fixed. These basis images determine the linear endomorphism."),
            Node("markedF", "The marked lowering operator", MarkedDefinition("markedF"), true,
                "For each arc, sum the enabled 21 to 12 transitions with coefficient one. The distinguished wall remains fixed. These basis images determine the linear endomorphism."),
            Node("h", "Descending the weight operator", DescentDefinition("h", "markedH"), true,
                "Apply S, then the marked weight operator, then Q, and multiply by the inverse of two in K."),
            Node("e", "Descending the raising operator", DescentDefinition("e", "markedE"), true,
                "Apply the same descent formula to the marked raising operator."),
            Node("f", "Descending the lowering operator", DescentDefinition("f", "markedF"), true,
                "Apply the same descent formula to the marked lowering operator."),
            Node("integerWeight", "The integer inversion weight", IntegerDefinition(), true,
                "The function level is the existing count of ordered 2-before-1 pairs. The function ones counts the twos, and length minus ones counts the ones. Both subtractions inside the weight are in the integers. The two arc contributions add and are independent of which wall is marked."),
            Node("literal_action", "Relations, physical identification and basis formulas", ActionFormula(), false,
                "Embed the coordinate delta basis injectively into the direct sum of the two-bin tensor spaces indexed by position and both lengths. The local swaps preserve filling. Their rational delta coefficients agree with the scalar extension in BinaryBinBaseChange, so the embedding intertwines all three endomorphisms. The supplied two-bin relations therefore hold on the marked space. Exchanging arcs exchanges the two summands of each action; translation changes only p. Thus all three operators commute with mark exchange and marked translation. The identities QS=2id and SQ=id+Jstar imply that S is injective, Jstar fixes its image, and S intertwines each descended action with its marked action. They transfer the commutator relations and translation symmetry to literal words. For the physical identification, the two wall positions and both arc intervals partition the cyclic sites. Bonds touching a wall contribute zero to F3. Every other bond belongs to exactly one arc interior, where encoding intertwines its swap with the cyclic site swap. Reindexing the complete bond sum gives f=F3, including the wraparound and empty-arc cases. The two marked lifts give identical basis images, and the inverse of two removes their duplication. Finally, weight_eq_level identifies the diagonal scalar with the integer inversion weight.")),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose) => Describe.Lean(
            DescribeId.Create("two-wall-sl2-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/TwoWallSl2." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Conjunction(params Formula[] items)
    {
        var result = items[^1];
        for (var i = items.Length - 2; i >= 0; i--) result = And(items[i], result);
        return result;
    }
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Cdot, Sp, Parenthesized(y));
    private static Formula Smul(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Cdot, Sp, Parenthesized(y));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), InMacro, type)), Sp, Parenthesized(body));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Cast(Formula x, Formula type) => Call("cast", x, type);
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula Environment(Formula body, bool charZero = true) => All("K", Call("Type"),
        Assumption(Call("Field", K), charZero ? Assumption(Call("CharZero", K), AB(body)) : AB(body)));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Tuple(params Formula[] items) => Parenthesized(Seq(
        items.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ifThenElse", Parenthesized(condition), yes, no);
    private static Formula Move(bool second, Formula c) => Call(second ? "rightMove" : "leftMove", c, J);

    private static Formula MoveDefinition(bool second)
    {
        var length = second ? CN : CM;
        var bin = second ? CV : CU;
        var i = F.Id("i");
        var swapped = Lambda("i", Fin(length), At(bin, At(Call("EquivSwap",
            Call("finMk", JVal, length), Call("finMk", Next, length)), i)));
        return AB(All("c", Coords, All("j", Fin(Sub(length, D(1))),
            Eq(Move(second, C), Tuple(CP, CM, CN, second ? CU : swapped, second ? swapped : CV)))));
    }

    private static Formula Condition(bool second, bool raising)
    {
        var bin = second ? CV : CU;
        var length = second ? CN : CM;
        return And(Eq(At(bin, Call("finMk", JVal, length)), Call(raising ? "false" : "true")),
            Eq(At(bin, Call("finMk", Next, length)), Call(raising ? "true" : "false")));
    }

    private static Formula Moves(bool second, bool raising, bool marked)
    {
        var length = second ? CN : CM;
        var target = marked ? MarkDelta(Move(second, C)) : LitDelta(Move(second, C));
        var coefficient = Mul(Cast(Next, K), Sub(Cast(length, K), Cast(Next, K)));
        return Sum("j", Fin(Sub(length, D(1))), If(Condition(second, raising),
            raising ? Smul(coefficient, target) : target, D(0)));
    }

    private static Formula MarkedDefinition(string name)
    {
        Formula image = name == "markedH"
            ? Smul(Add(Cast(Call("weight", CU), K), Cast(Call("weight", CV), K)), MarkDelta(C))
            : Add(Moves(false, name == "markedE", true), Moves(true, name == "markedE", true));
        return Environment(All("c", Coords, Eq(At(Op(name), MarkDelta(C)), image)), false);
    }

    private static Formula DescentDefinition(string name, string marked) => Environment(Eq(Op(name),
        Smul(Call("inverse", Cast(D(2), K)),
            Call("comp", Op("Q"), Call("comp", Op(marked), Op("S"))))), false);

    private static Formula IntegerDefinition()
    {
        Formula binWeight(Formula bin, Formula length) => Sub(Mul(D(2), Cast(Call("level", bin), Ints)),
            Mul(Cast(Call("ones", bin), Ints), Sub(Cast(length, Ints), Cast(Call("ones", bin), Ints))));
        return AB(All("c", Coords, Eq(Call("integerWeight", C),
            Add(binWeight(CU, CM), binWeight(CV, CN)))));
    }

    private static Formula Relations(bool marked) => Call("Sl2Relations",
        Op(marked ? "markedH" : "h"), Op(marked ? "markedE" : "e"), Op(marked ? "markedF" : "f"));
    private static Formula Commutes(Formula x, Formula y) => Call("Commute", x, y);
    private static Formula TripleCommutes(Formula shift, bool marked) => Conjunction(
        Commutes(shift, Op(marked ? "markedH" : "h")),
        Commutes(shift, Op(marked ? "markedE" : "e")),
        Commutes(shift, Op(marked ? "markedF" : "f")));

    private static Formula BasisFormula() => All("c", Coords, Conjunction(
        Eq(At(Op("h"), LitDelta(C)), Smul(Cast(Call("integerWeight", C), K), LitDelta(C))),
        Eq(At(Op("e"), LitDelta(C)), Add(Moves(false, true, false), Moves(true, true, false))),
        Eq(At(Op("f"), LitDelta(C)), Add(Moves(false, false, false), Moves(true, false, false)))));

    private static Formula ActionFormula() => Environment(Conjunction(
        Relations(true),
        Conjunction(Commutes(Op("Jstar"), Op("markedH")),
            Commutes(Op("Jstar"), Op("markedE")), Commutes(Op("Jstar"), Op("markedF")),
            All("t", Sites, TripleCommutes(Shift(true, T), true))),
        Relations(false),
        Eq(Op("f"), Op("F3")),
        And(All("t", Sites, TripleCommutes(Shift(false, T), false)), TripleCommutes(Op("U"), false)),
        BasisFormula()));
}
