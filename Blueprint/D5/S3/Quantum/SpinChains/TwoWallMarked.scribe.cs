using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TwoWallMarkedDocument : IScribeDocumentDefinition
{
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("K");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Sites => Call("Pos", A, B);
    private static Formula Words => Call("Word", A, B);
    private static Formula Marked => Call("MarkedWord", A, B);
    private static Formula Coords => Call("Coordinates", A, B);
    private static Formula Wall => Call("wall");
    private static Formula Two => Call("two");
    private static Formula One => Call("one");
    private static Formula Bool => Call("Bool");
    private static Formula X => F.Id("x");
    private static Formula C => F.Id("c");
    private static Formula P => F.Id("p");
    private static Formula T => F.Id("t");
    private static Formula W => F.Id("w");
    private static Formula I => F.Id("i");
    private static Formula CM => Call("m", C);
    private static Formula CN => Call("n", C);
    private static Formula CP => Call("p", C);
    private static Formula CU => Call("u", C);
    private static Formula CV => Call("v", C);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinguishing either wall identifies literal cyclic words with ordered binary arcs and gives a free double cover compatible with translation.",
        H("Marked walls and ordered binary arcs"),
        Blocks(
            Paragraph(Text("Fix natural numbers a,b and put L=a+b+2. Positions, literal words and their delta basis are those of TwoWallWords. A mark distinguishes one of the two wall positions without changing the literal word. Binary true denotes letter two and false denotes letter one. Coordinates store p,m,n,u,v with m+n=a+b; thus n=a+b−m and m<L−1. This redundant length coordinate is uniquely determined and includes both empty-arc cases. The function ones is the existing count of true entries in a binary word. All equalities of positions use ZMod(L); natural-number subtractions in lengths and indices are truncated subtraction.")),
            Node("MarkedWord", "Distinguishing one wall", MarkedFormula(), true,
                "The subtype retains the counted literal word and a position occupied by a wall."),
            Node("otherWall", "The unique other wall", OtherFormula(), true,
                "There are exactly two wall positions. Given the distinguished position, exactly one other wall remains. Choose denotes classical choice from the displayed unique specification."),
            Node("J", "Exchanging the distinguished wall", AB(All("x", Marked,
                Eq(Call("J", X), Pair(Word(X), Call("otherWall", X))))), true,
                "The underlying literal word is retained and its other wall becomes the distinguished wall."),
            Node("markedRotate", "Translating a marked word", MarkedRotateFormula(), true,
                "The forward map translates the word and its mark by t. The inverse translates by minus t. The marked letter stays a wall."),
            Node("MarkedSpace", "Linear combinations of marked words", AB(All("K", Call("Type"),
                Assumption(Call("Zero", K), Eq(Call("MarkedSpace", K, A, B), Call("Finsupp", Marked, K))))), true,
                "The marked vector space has one delta basis vector for each choice of a literal word and a wall mark."),
            Node("markedDelta", "Marked delta vectors", FieldAB(All("x", Marked,
                Eq(Call("markedDelta", K, X), Call("single", X, D(1))))), true,
                "The coefficient is one at the indicated marked word and zero at all other labels."),
            Node("Q", "Forgetting the mark", FieldAB(Eq(Op("Q"),
                Call("lmapDomain", K, K, Lambda("x", Marked, Word(X))))), true,
                "Linear pushforward sends each marked delta vector to the delta vector of its underlying literal word."),
            Node("S", "Summing the two marked lifts", SFormula(), true,
                "LinearCombination extends the displayed basis images linearly. The sum is over the subtype of wall positions, so each literal word has precisely two summands."),
            Node("Jstar", "The linear mark exchange", FieldAB(Eq(Op("Jstar"),
                Call("lmapDomain", K, K, Lambda("x", Marked, Call("J", X))))), true,
                "The map pushes basis labels forward under the exchange of marks."),
            Node("markedTranslation", "Linear translation on the cover", FieldAB(All("t", Sites,
                Eq(Call("markedTranslation", K, T), Call("lmapDomain", K, K, Call("markedRotate", T))))), true,
                "Translation permutes the marked basis labels."),
            Node("markedU", "The one-site marked shift", FieldAB(Eq(Op("markedU"),
                Call("markedTranslation", K, D(1)))), true,
                "This is the right shift by one site on the marked cover."),
            Node("marked_descent", "A free double cover and the descent identities", DescentFormula(), false,
                "The other wall of the other wall is the original mark, and the two marks are distinct. Translation preserves this unique pairing. On a marked delta vector, S after Q sums that vector and the vector with the other mark. On a literal delta vector, Q after S adds that vector twice. Translation sends the two marked lifts bijectively to the two lifts of the translated word; this gives the two intertwining identities for every displacement and hence for the one-site shifts. These identities hold over every field, including characteristic two."),
            Node("Coordinates", "The two ordered binary arcs", CoordinatesFormula(), true,
                "The dependent tuple consists of p,m,n,u,v. The first binary word has length m, the second has length n, and their numbers of true entries add to b. The proof fields are the length and filling equalities; no positivity is imposed on either arc."),
            Node("encode", "Placing the two arcs on the cycle", EncodeFormula(), true,
                "Starting at p, place wall,u,wall,v at consecutive offsets. The displayed piecewise expression reads the unique residue d in [0,L). The two wall offsets and the two interior intervals partition all positions, including when either interval is empty. Reindexing the counts gives a ones, b twos and two walls."),
            Node("decode", "Reading the arcs from a marked word", DecodeFormula(), true,
                "The nonzero residue of otherWall(x)−mark(x) has representative d between 1 and L−1. Its predecessor is m; the complementary nonwall length is n. The arcs contain no walls, so equality with letter two recovers their Boolean entries. Reconstructing every site also recovers the total number b of true entries."),
            Node("coordinateEquiv", "The marked-word coordinate equivalence", AB(
                And(Eq(Call("forward", Call("coordinateEquiv", A, B)),
                        Lambda("c", Coords, Enc(C))),
                    Eq(Call("inverse", Call("coordinateEquiv", A, B)),
                        Lambda("x", Marked, Call("decode", X))))), true,
                "Encoding and decoding are mutually inverse; the forward map is encode and the inverse map is decode."),
            Node("coordinateSwap", "Mark exchange in arc coordinates", AB(All("c", Coords,
                Eq(Swap(C), Tuple(Add(CP, Cast(Add(CM, D(1)))), CN, CM, CV, CU)))), true,
                "The second wall becomes the starting position, the two lengths exchange places, and the two binary words exchange places. The length and filling certificates follow by commutativity of addition."),
            Node("coordinateRotate", "Rotation acts only on the position", AB(All("t", Sites, All("c", Coords,
                Eq(Rot(T, C), Tuple(Add(CP, T), CM, CN, CU, CV))))), true,
                "Both lengths and both binary words are retained; only p changes to p+t."),
            Node("marked_coordinates", "Round trips, layouts and coordinate symmetries", CoordinateTheorem(), false,
                "The representative of the distance to the other wall determines the first arc length uniquely. Reading and replacing all sites gives both inverse laws. Exchanging the two arcs shifts the starting position by m+1; after the second exchange the displacement is L and therefore zero. The two marks differ, which proves freeness in coordinates. Translation changes only the starting position and commutes with this exchange. All quantifiers include m=0, n=0 and a=b=0.")),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose) => Describe.Lean(
            DescribeId.Create("two-wall-marked-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/TwoWallMarked." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => Seq(Neg, Parenthesized(Eq(x, y)));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(
        Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(
        Parenthesized(x), FormulaLogicOperator.Or, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(
        Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Pair(Formula x, Formula y) => Tuple(x, y);
    private static Formula Tuple(params Formula[] items) => Parenthesized(Seq(
        items.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()));
    private static Formula Cast(Formula x) => Call("natCast", Parenthesized(x));
    private static Formula Fin(Formula x) => Call("Fin", x);
    private static Formula Bin(Formula x) => new Formula.TypeArrow(Fin(x), Bool);
    private static Formula Assumption(Formula x, Formula body) => Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula FieldAB(Formula body) => All("K", Call("Type"), Assumption(Call("Field", K), AB(body)));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), InMacro, type)), Sp, Parenthesized(body));
    private static Formula Word(Formula x) => Call("word", x);
    private static Formula Mark(Formula x) => Call("mark", x);
    private static Formula LetterAt(Formula w, Formula p) => At(Call("coe", w), p);
    private static Formula Enc(Formula c) => Call("encode", c);
    private static Formula Swap(Formula c) => Call("coordinateSwap", c);
    private static Formula Rot(Formula t, Formula c) => Call("coordinateRotate", t, c);
    private static Formula Op(string name) => Call(name, K, A, B);
    private static Formula Comp(Formula x, Formula y) => Seq(x, Sp, Circ, Sp, y);
    private static Formula Smul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Identity => Call("id");
    private static Formula EncAt(Formula p) => LetterAt(Word(Enc(C)), p);
    private static Formula Read(Formula w, Formula p) => Call("decide", Eq(LetterAt(w, p), Two));
    private static Formula BinaryLetter(Formula bit) => Call("ite", bit, Two, One);
    private static Formula Both(params Formula[] clauses) => clauses.Aggregate((x, y) => And(x, y));

    private static Formula MarkedFormula() => AB(Eq(Marked, Call("Subtype",
        Lambda("x", Call("Prod", Words, Sites), Eq(LetterAt(Call("first", X), Call("second", X)), Wall)))));

    private static Formula OtherFormula()
    {
        var q = F.Id("q"); var r = F.Id("r");
        var spec = Lambda("q", Sites, And(Ne(q, Mark(X)),
            And(Eq(LetterAt(Word(X), q), Wall), All("r", Sites,
                Imp(Eq(LetterAt(Word(X), r), Wall), Or(Eq(r, Mark(X)), Eq(r, q)))))));
        return AB(All("x", Marked, Eq(Call("otherWall", X), Call("Choose", spec))));
    }
    private static Formula MarkedRotateFormula() => AB(All("t", Sites, All("x", Marked,
        And(Eq(At(Call("markedRotate", T), X), Pair(At(Call("rotate", T), Word(X)), Add(Mark(X), T))),
            Eq(At(Call("inverse", Call("markedRotate", T)), X),
                Pair(At(Call("inverse", Call("rotate", T)), Word(X)), Sub(Mark(X), T)))))));

    private static Formula SFormula()
    {
        var wallPositions = Call("Subtype", Lambda("p", Sites, Eq(LetterAt(W, P), Wall)));
        return FieldAB(Eq(Op("S"), Call("linearCombination", K, Lambda("w", Words,
            Sum("p", wallPositions, Call("markedDelta", K, Pair(W, Call("coe", P))))))));
    }
    private static Formula DescentFormula()
    {
        var involutive = All("x", Marked, Eq(Call("J", Call("J", X)), X));
        var free = All("x", Marked, Ne(Call("J", X), X));
        var equivariant = All("t", Sites, All("x", Marked,
            Eq(At(Call("markedRotate", T), Call("J", X)), Call("J", At(Call("markedRotate", T), X)))));
        var qs = Eq(Comp(Op("Q"), Op("S")), Smul(Call("scalar", K, D(2)), Identity));
        var sq = Eq(Comp(Op("S"), Op("Q")), Add(Identity, Op("Jstar")));
        var rs = All("t", Sites, Eq(Comp(Call("markedTranslation", K, T), Op("S")),
            Comp(Op("S"), Call("translation", K, T))));
        var qr = All("t", Sites, Eq(Comp(Op("Q"), Call("markedTranslation", K, T)),
            Comp(Call("translation", K, T), Op("Q"))));
        var us = Eq(Comp(Op("markedU"), Op("S")), Comp(Op("S"), Op("U")));
        var qu = Eq(Comp(Op("Q"), Op("markedU")), Comp(Op("U"), Op("Q")));
        return FieldAB(Both(involutive, free, equivariant, qs, sq, rs, qr, us, qu));
    }
    private static Formula CoordinatesFormula()
    {
        var m = F.Id("m"); var n = F.Id("n");
        var fields = Call("Sigma", Sites, Lambda("p", Sites,
            Call("Sigma", Nats, Lambda("m", Nats,
                Call("Sigma", Nats, Lambda("n", Nats, Call("Prod", Bin(m), Bin(n))))))));
        return AB(Eq(Coords, Call("Subtype", Lambda("c", fields,
            And(Eq(Add(CM, CN), Add(A, B)), Eq(Add(Call("ones", CU), Call("ones", CV)), B))))));
    }
    private static Formula EncodeFormula()
    {
        var q = F.Id("q"); var d = F.Id("d");
        var dDef = Call("val", Sub(q, CP));
        var body = Call("ite", Or(Eq(d, D(0)), Eq(d, Add(CM, D(1)))), Wall,
            Call("ite", new Formula.Relation(d, FormulaRelationOperator.LessThanOrEqual, CM),
                BinaryLetter(At(CU, Call("finIndex", Sub(d, D(1))))),
                BinaryLetter(At(CV, Call("finIndex", Sub(Sub(d, CM), D(2)))))));
        return AB(All("c", Coords, And(Eq(Mark(Enc(C)), CP),
            All("q", Sites, All("d", Nats, Imp(Eq(d, dDef), Eq(EncAt(q), body)))))));
    }
    private static Formula DecodeFormula()
    {
        var d = F.Id("d"); var m = Sub(d, D(1)); var n = Sub(Add(A, B), Parenthesized(m));
        var mark = Mark(X); var word = Word(X);
        var u = Lambda("i", Fin(m), Read(word, Add(mark, Cast(Add(Call("val", I), D(1))))));
        var v = Lambda("i", Fin(n), Read(word, Add(mark, Cast(Add(Add(Parenthesized(m), D(2)), Call("val", I))))));
        return AB(All("x", Marked, All("d", Nats,
            Imp(Eq(d, Call("val", Sub(Call("otherWall", X), mark))),
                Eq(Call("decode", X), Tuple(mark, m, n, u, v))))));
    }
    private static Formula CoordinateTheorem()
    {
        var left = All("c", Coords, Eq(Call("decode", Enc(C)), C));
        var right = All("x", Marked, Eq(Enc(Call("decode", X)), X));
        var bounds = All("c", Coords,
            And(new Formula.Relation(CM, FormulaRelationOperator.LessThan, Add(Add(A, B), D(1))),
                Eq(CN, Sub(Add(A, B), CM))));
        var layout = All("c", Coords, Both(Eq(EncAt(CP), Wall),
            Eq(EncAt(Add(CP, Cast(Add(CM, D(1))))), Wall),
            All("i", Fin(CM), Eq(EncAt(Add(CP, Cast(Add(Call("val", I), D(1))))), BinaryLetter(At(CU, I)))),
            All("i", Fin(CN), Eq(EncAt(Add(CP, Cast(Add(Add(CM, D(2)), Call("val", I))))), BinaryLetter(At(CV, I))))));
        var swap = All("c", Coords, Eq(Enc(Swap(C)), Call("J", Enc(C))));
        var involutive = All("c", Coords, Eq(Swap(Swap(C)), C));
        var free = All("c", Coords, Ne(Swap(C), C));
        var rotation = All("t", Sites, All("c", Coords, Eq(Enc(Rot(T, C)), At(Call("markedRotate", T), Enc(C)))));
        var commute = All("t", Sites, All("c", Coords, Eq(Rot(T, Swap(C)), Swap(Rot(T, C)))));
        return AB(Both(left, right, bounds, layout, swap, involutive, free, rotation, commute));
    }
}
