using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TwoWallWeightsDocument : IScribeDocumentDefinition
{
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("K");
    private static Formula W => F.Id("w");
    private static Formula P => F.Id("p");
    private static Formula C => F.Id("c");
    private static Formula I => F.Id("i");
    private static Formula S => F.Id("s");
    private static Formula X => F.Id("x");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Words => Call("Word", A, B);
    private static Formula Sites => Call("Pos", A, B);
    private static Formula Coords => Call("Coordinates", A, B);
    private static Formula FinThree => Call("Fin", D(3));
    private static Formula Couplings => new Formula.TypeArrow(FinThree, K);
    private static Formula Weight(Formula w) => Call("wordWeight", w);
    private static Formula Encoded(Formula c) => Call("word", Call("encode", c));
    private static Formula Delta(Formula w) => Call("delta", K, w);
    private static Formula Op(string name) => Call(name, K, A, B);
    private static Formula BondSum => Call("F", K, A, B, I);
    private static Formula Coupled => Call("T", K, A, B, X);
    private static Formula Filter(Formula s) => Call("weightLE", Op("h"), s);
    private static Formula Exponent => Add(Mul(A, B), D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer inversion weights control the exact local bond moves and the nilpotence of the literal two-wall action.",
        H("Weight drops and nilpotence for two-wall words"),
        Blocks(
            Paragraph(Text("Let a,b be natural numbers. Literal words contain a ones, b twos and two walls on the cyclic sites Pos(a,b). The binary coordinates between the walls use true for two and false for one. The operator h and its integer coordinate weight are those of TwoWallSl2. In F(K,a,b,i), the indices 0,1,2 denote the physical operators F1,F2,F3, with input pairs 32,13,21 respectively. All operator statements below hold over every field K of characteristic zero. Submodule inequalities denote inclusion.")),
            Node("wordWeight", "The weight of a literal word", WeightDefinition(), true,
                "Choose a wall of w by classical choice, mark it, decode the two arcs and apply integerWeight. The set supplied to choose consists of the sites carrying a wall and is nonempty because there are exactly two walls. The tuple in the formula is regarded as a marked word; its wall certificate is implicit. The coordinate identity below shows that the result agrees with integerWeight for every marking."),
            Node("weight_structure", "Integral weights and their bounds", StructureFormula(), false,
                "The coordinate delta formula identifies the chosen integer weight with the eigenvalue of h, independently of the chosen wall. For an arc of length m with r twos, its inversion count lies between zero and r(m−r); hence its weight lies between −r(m−r) and r(m−r). Adding the two arc bounds and the nonnegative cross terms gives the interval [−ab,ab]. The finite image of wordWeight on all literal words supplies an integral weight set whose eigenspaces span the whole space."),
            Node("weight_control", "Exact bond drops, filtration descent and nilpotence", ControlFormula(), false,
                "Write the contribution of a binary arc B as chi(B)=2 level(B)−ones(B)(length(B)−ones(B)). Prepending a two adds the number of ones in B, and appending a two subtracts it. Prepending a one subtracts the number of twos, and appending a one adds it. For 32 to 23, mark the wall in the source and move the initial two from the first arc to the end of the second arc; the two changes add to −a. The reverse wall move with a one yields the 13 to 31 change −b. Inside either arc, 21 to 12 removes one inversion and gives −2; equivalently the same drop follows from the h,F3 commutator and the positive delta coefficient of an enabled bond. When a,b are at least two, every term in every bond sum drops weight by at least two. The delta basis description of weightLE extends this to all vectors and every linear combination T. After ab+1 steps the top possible weight ab is sent strictly below −ab, where the filtration is zero. The F3 conclusion holds for every a,b, including zero and one.")),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose) => Describe.Lean(
            DescribeId.Create("two-wall-weights-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/TwoWallWeights." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args)
    {
        var symbol = name == "F3" ? Seq(Operatorname, Grp(F.Id("F"), D(3)))
            : Seq(Operatorname, Grp(F.Id(name)));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
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
    private static Formula Pow(Formula x) => new Formula.Power(Parenthesized(x), Exponent);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Environment(Formula body) => All("K", Call("Type"),
        Assumption(Call("Field", K), Assumption(Call("CharZero", K), AB(body))));

    private static Formula WeightDefinition()
    {
        var walls = new Formula.SetBuilder(P, P,
            Seq(Sites, Sp, Land, Sp, Parenthesized(Eq(At(W, P), Call("wall")))));
        var marked = Parenthesized(Seq(W, Comma, Sp, Call("choose", walls)));
        return AB(All("w", Words, Eq(Weight(W),
            Call("integerWeight", Call("decode", marked)))));
    }

    private static Formula StructureFormula() => Environment(Conjunction(
        All("c", Coords, Eq(Weight(Encoded(C)), Call("integerWeight", C))),
        All("w", Words, Eq(At(Op("h"), Delta(W)),
            Mul(Call("cast", Weight(W), K), Delta(W)))),
        Call("IntegralWeights", Op("h")),
        All("w", Words, And(Le(Seq(Minus, Parenthesized(Mul(A, B))), Weight(W)),
            Le(Weight(W), Mul(A, B))))));

    private static Formula Drop(byte i, Formula amount) => All("w", Words, All("p", Sites,
        Implies(Call("Allowed", D(i), W, P),
            Eq(Weight(Call("swapWord", P, W)), Sub(Weight(W), amount)))));

    private static Formula Lowers(Formula op) =>
        Le(Call("map", Filter(S), op), Filter(Sub(S, D(2))));

    private static Formula ControlFormula() => Environment(Conjunction(
        Drop(0, A), Drop(1, B), Drop(2, D(2)),
        Implies(Le(D(2), A), Implies(Le(D(2), B), Conjunction(
            All("i", FinThree, All("s", Ints, Lowers(BondSum))),
            All("x", Couplings, All("s", Ints, Lowers(Coupled))),
            All("x", Couplings, Eq(Pow(Coupled), D(0)))))),
        Eq(Pow(Op("F3")), D(0))));
}
