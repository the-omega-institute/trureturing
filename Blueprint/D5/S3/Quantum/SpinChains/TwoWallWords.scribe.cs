using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TwoWallWordsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahn2022eclectic");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("K");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Letter => Call("Letter");
    private static Formula Sites => Call("Pos", A, B);
    private static Formula Words => Call("Word", A, B);
    private static Formula RawWords => new Formula.TypeArrow(Sites, Letter);
    private static Formula Vectors => Call("Space", K, A, B);
    private static Formula Length => PlusOf(PlusOf(A, B), D(2));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal cyclic words with two walls carry the three eclectic bond operators and a commuting right shift.",
        H("Two walls in the literal cyclic word space"),
        Blocks([
            Paragraph(Text("Let a and b be natural numbers and L = a+b+2. The positions form ZMod(L). The letters one, two and wall denote the physical letters 1, 2 and 3, respectively; their Fin(3) encodings are 0, 1 and 2. Words retain their positions and are not identified under rotation. The vector space over any field K consists of finite linear combinations of counted words. Its delta vector at w has coefficient one at w and zero elsewhere. Endomorphism multiplication means composition, with the right factor acting first.")),
            Node("Letter", "The three-letter type", Eq(Letter, Call("Fin", D(3))), true,
                "The letter type has exactly three elements."),
            Node("one", "Letter one", Eq(Call("one"), D(0)), true, "The first encoding denotes letter 1."),
            Node("two", "Letter two", Eq(Call("two"), D(1)), true, "The second encoding denotes letter 2."),
            Node("wall", "The wall", Eq(Call("wall"), D(2)), true, "The third encoding denotes the wall 3."),
            Node("Pos", "Cyclic positions", AB(Eq(Sites, Call("ZMod", Length))), true,
                "Addition of positions is taken modulo L, so the last and first positions are adjacent."),
            Node("count", "Counting a letter", CountFormula(), true,
                "Each site contributes one exactly when its letter equals c."),
            Node("Word", "Counted literal words", WordFormula(), true,
                "The subtype retains exactly a ones, b twos and two walls. The three count certificates restrict the complete function space. The finite ambient function type and decidable count predicates give Word its inherited Fintype instance."),
            Node("permute", "Transport along a site permutation", PermuteFormula(), true,
                "The forward map composes a word with the inverse site permutation; the inverse map composes with the permutation itself. Reindexing the finite count sum preserves every letter count, so both maps land in the counted subtype."),
            Node("rotate", "Right rotation", AB(All("t", Sites, Eq(Call("rotate", F.Id("t")),
                Call("permute", Call("addRight", F.Id("t")))))), true,
                "The position map addRight(t) sends p to p+t. The transported word thus reads w(p−t), giving the source's right-shift convention."),
            Node("swapWord", "Swapping a cyclic bond", AB(All("p", Sites, Eq(Call("swapWord", F.Id("p")),
                Call("permute", Call("swap", F.Id("p"), PlusOf(F.Id("p"), D(1))))))), true,
                "The same permutation exchanges both cyclically adjacent sites and fixes all other sites."),
            Node("inputPair", "Oriented allowed inputs", Eq(Call("inputPair"), Call("vector3",
                Pair(Call("wall"), Call("two")), Pair(Call("one"), Call("wall")),
                Pair(Call("two"), Call("one")))), true,
                "In arXiv:2112.04506v1, Section 2.1, Eq. (2.3), the three transitions are 32 to 23, 13 to 31, and 21 to 12. Every other input pair is annihilated.", true),
            Node("Allowed", "The input-pair predicate", AllowedFormula(), true,
                "The test reads the ordered pair at p and p+1 before exchanging the sites.", true),
            Node("allowedDecidable", "Decidable input test", AB(All("i", Call("Fin", D(3)),
                All("w", Words, All("p", Sites, Eq(Call("allowedDecidable", F.Id("i"), F.Id("w"), F.Id("p")),
                    Call("inferInstance", Call("Decidable", Call("Allowed", F.Id("i"), F.Id("w"), F.Id("p"))))))))), true,
                "Equality of the finite letters decides both parts of the input test."),
            Node("Space", "The word vector space", AB(All("K", Call("Type"),
                Assumption(Call("Zero", K), Eq(Vectors, Call("Finsupp", Words, K))))), true,
                "Finsupp consists of functions with finite support. Since the word type is finite, every coefficient function has finite support."),
            Node("basis", "The canonical word basis", FieldAB(Eq(Call("basis", K, A, B),
                Call("FinsuppBasisSingleOne", K, Words))), true,
                "The standard finitely supported function basis is indexed by all counted words. Its coordinates give unique expansions into delta vectors."),
            Node("delta", "Delta vectors", FieldAB(All("w", Words,
                Eq(Delta(F.Id("w")), At(Call("basis", K, A, B), F.Id("w"))))), true,
                "Delta vectors are the canonical basis of the finitely supported function space."),
            Node("bond", "One local transition", BondFormula(), true,
                "The local action is the delta vector at the exchanged word when the input test succeeds, and zero otherwise. This is the action in Eq. (2.3), restricted to words with two walls.", true),
            Node("F", "The bond sum", FFormula(), true,
                "LinearCombination extends the displayed image of each delta vector linearly. The sum runs over all positions, as in Eq. (2.2); different bonds leading to the same word contribute separately.", true),
            Node("F1", "The first bond operator", FieldAB(Eq(Op("F1"), Call("F", K, A, B, D(0)))), true,
                "F1 sums the transitions 32 to 23.", true),
            Node("F2", "The second bond operator", FieldAB(Eq(Op("F2"), Call("F", K, A, B, D(1)))), true,
                "F2 sums the transitions 13 to 31.", true),
            Node("F3", "The third bond operator", FieldAB(Eq(Op("F3"), Call("F", K, A, B, D(2)))), true,
                "F3 sums the transitions 21 to 12.", true),
            Node("T", "The coupled eclectic operator", TFormula(), true,
                "The three couplings multiply the three bond sums, as in Eq. (2.2). No nonzero-coupling or characteristic-zero assumption is needed for this action.", true),
            Node("translation", "Linear translation", FieldAB(All("t", Sites,
                Eq(Call("translation", K, F.Id("t")), Call("lmapDomain", K, K, Call("rotate", F.Id("t")))))), true,
                "The map pushes each basis label forward by right rotation."),
            Node("U", "The one-site right shift", FieldAB(Eq(Op("U"), Call("translation", K, D(1)))), true,
                "Section 2.2, Eq. (2.9), uses U on the elementary state j1…jL to give jL j1…j(L−1). This is rotation by one in the literal word coordinates.", true),
            Node("cyclic_action", "Count preservation, delta actions and translation symmetry", ActionFormula(), false,
                "A swap is a permutation of sites, so finite-sum reindexing preserves every count. Translation carries the bond at p to the bond at p+t, with the same oriented input test and exchanged output. Reindexing the complete bond sum therefore gives commutation. Repeated right shifts add their displacements in ZMod(L); displacement L is zero. The coupling formula inherits commutation by linearity."),
            ..MarkedContent()]),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("two-wall-words-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/TwoWallWords." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula PlusOf(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Smul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Assumption(Formula x, Formula body) => Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula FieldAB(Formula body) => All("K", Call("Type"), Assumption(Call("Field", K), AB(body)));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), InMacro, type)), Sp, Parenthesized(body));
    private static Formula Delta(Formula w) => Call("delta", K, w);
    private static Formula Op(string name) => Call(name, K, A, B);
    private static Formula Coe(Formula w) => Call("coe", w);
    private static Formula Count(Formula c, Formula w) => Call("count", c, w);
    private static Formula Commuting(Formula x, Formula y) => Eq(Mul(x, y), Mul(y, x));

    private static Formula CountFormula()
    {
        var c = F.Id("c"); var w = F.Id("w"); var p = F.Id("p");
        return AB(All("c", Letter, All("w", RawWords, Eq(Count(c, w),
            Sum("p", Sites, Call("ite", Eq(At(w, p), c), D(1), D(0)))))));
    }
    private static Formula WordFormula()
    {
        var w = F.Id("w");
        return AB(Eq(Words, Call("Subtype", Lambda("w", RawWords,
            And(Eq(Count(Call("one"), w), A), And(Eq(Count(Call("two"), w), B),
                Eq(Count(Call("wall"), w), D(2))))))));
    }
    private static Formula PermuteFormula()
    {
        var e = F.Id("e"); var w = F.Id("w"); var p = F.Id("p");
        var equiv = Call("permute", e);
        return AB(All("e", Call("Perm", Sites), All("w", Words, All("p", Sites,
            And(Eq(At(Coe(At(equiv, w)), p), At(Coe(w), At(Call("inverse", e), p))),
                Eq(At(Coe(At(Call("inverse", equiv), w)), p), At(Coe(w), At(e, p))))))));
    }
    private static Formula AllowedFormula()
    {
        var i = F.Id("i"); var w = F.Id("w"); var p = F.Id("p");
        return AB(All("i", Call("Fin", D(3)), All("w", Words, All("p", Sites,
            Iff(Call("Allowed", i, w, p), And(Eq(At(Coe(w), p), Call("first", Call("inputPair", i))),
                Eq(At(Coe(w), PlusOf(p, D(1))), Call("second", Call("inputPair", i)))))))));
    }
    private static Formula BondFormula()
    {
        var i = F.Id("i"); var p = F.Id("p"); var w = F.Id("w");
        return FieldAB(All("i", Call("Fin", D(3)), All("p", Sites, All("w", Words,
            Eq(Call("bond", K, i, p, w), Call("ite", Call("Allowed", i, w, p),
                Delta(At(Call("swapWord", p), w)), D(0)))))));
    }
    private static Formula FFormula() => FieldAB(All("i", Call("Fin", D(3)),
        Eq(Call("F", K, A, B, F.Id("i")), Call("linearCombination", K,
            Lambda("w", Words, Sum("p", Sites, Call("bond", K, F.Id("i"), F.Id("p"), F.Id("w"))))))));
    private static Formula TFormula()
    {
        var xi = F.Id("xi");
        return FieldAB(All("xi", new Formula.TypeArrow(Call("Fin", D(3)), K),
            Eq(Call("T", K, A, B, xi), PlusOf(PlusOf(Smul(At(xi, D(0)), Op("F1")),
                Smul(At(xi, D(1)), Op("F2"))), Smul(At(xi, D(2)), Op("F3"))))));
    }
    private static Formula ActionFormula()
    {
        var c = F.Id("c"); var p = F.Id("p"); var w = F.Id("w");
        var t = F.Id("t"); var i = F.Id("i"); var xi = F.Id("xi");
        var counts = All("c", Letter, All("p", Sites, All("w", RawWords,
            Eq(Count(c, Lambda("q", Sites, At(w, At(Call("swap", p, PlusOf(p, D(1))), F.Id("q"))))), Count(c, w)))));
        var translation = All("t", Sites, All("w", Words,
            Eq(At(Call("translation", K, t), Delta(w)), Delta(At(Call("rotate", t), w)))));
        var shift = All("w", Words, Eq(At(Op("U"), Delta(w)), Delta(At(Call("rotate", D(1)), w))));
        var bonds = All("i", Call("Fin", D(3)), All("w", Words,
            Eq(At(Call("F", K, A, B, i), Delta(w)), Sum("p", Sites, Call("bond", K, i, p, w)))));
        var periodic = Eq(new Formula.Power(Op("U"), Length), D(1));
        var commute = All("i", Call("Fin", D(3)), Commuting(Op("U"), Call("F", K, A, B, i)));
        var coupled = All("xi", new Formula.TypeArrow(Call("Fin", D(3)), K),
            Commuting(Op("U"), Call("T", K, A, B, xi)));
        return FieldAB(And(counts, And(translation, And(shift, And(bonds, And(periodic, And(commute, coupled)))))));
    }

    private static Formula MarkedA => F.Id("a");
    private static Formula MarkedB => F.Id("b");
    private static Formula MarkedK => F.Id("K");
    private static Formula MarkedNats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula MarkedSites => MarkedCall("Pos", MarkedA, MarkedB);
    private static Formula MarkedWords => MarkedCall("Word", MarkedA, MarkedB);
    private static Formula MarkedMarked => MarkedCall("MarkedWord", MarkedA, MarkedB);
    private static Formula MarkedCoords => MarkedCall("Coordinates", MarkedA, MarkedB);
    private static Formula MarkedWall => MarkedCall("wall");
    private static Formula MarkedTwo => MarkedCall("two");
    private static Formula MarkedOne => MarkedCall("one");
    private static Formula MarkedBool => MarkedCall("Bool");
    private static Formula MarkedX => F.Id("x");
    private static Formula MarkedC => F.Id("c");
    private static Formula MarkedP => F.Id("p");
    private static Formula MarkedT => F.Id("t");
    private static Formula MarkedW => F.Id("w");
    private static Formula MarkedI => F.Id("i");
    private static Formula MarkedCM => MarkedCall("m", MarkedC);
    private static Formula MarkedCN => MarkedCall("n", MarkedC);
    private static Formula MarkedCP => MarkedCall("p", MarkedC);
    private static Formula MarkedCU => MarkedCall("u", MarkedC);
    private static Formula MarkedCV => MarkedCall("v", MarkedC);

    private static DocumentBlock[] MarkedContent() => [
            Paragraph(Text("Fix natural numbers a,b and put L=a+b+2. Positions, literal words and their delta basis are those of TwoWallWords. A mark distinguishes one of the two wall positions without changing the literal word. Binary true denotes letter two and false denotes letter one. Coordinates store p,m,n,u,v with m+n=a+b; thus n=a+b−m and m<L−1. This redundant length coordinate is uniquely determined and includes both empty-arc cases. The function ones is the existing count of true entries in a binary word. All equalities of positions use ZMod(L); natural-number subtractions in lengths and indices are truncated subtraction.")),
            MarkedNode("MarkedWord", "Distinguishing one wall", MarkedMarkedFormula(), true,
                "The subtype retains the counted literal word and a position occupied by a wall."),
            MarkedNode("otherWall", "The unique other wall", MarkedOtherFormula(), true,
                "There are exactly two wall positions. Given the distinguished position, exactly one other wall remains. Choose denotes classical choice from the displayed unique specification."),
            MarkedNode("J", "Exchanging the distinguished wall", MarkedAB(MarkedAll("x", MarkedMarked,
                MarkedEq(MarkedCall("J", MarkedX), MarkedPair(MarkedWord(MarkedX), MarkedCall("otherWall", MarkedX))))), true,
                "The underlying literal word is retained and its other wall becomes the distinguished wall."),
            MarkedNode("markedRotate", "Translating a marked word", MarkedMarkedRotateFormula(), true,
                "The forward map translates the word and its mark by t. The inverse translates by minus t. The marked letter stays a wall."),
            MarkedNode("MarkedSpace", "Linear combinations of marked words", MarkedAB(MarkedAll("K", MarkedCall("Type"),
                MarkedAssumption(MarkedCall("Zero", MarkedK), MarkedEq(MarkedCall("MarkedSpace", MarkedK, MarkedA, MarkedB), MarkedCall("Finsupp", MarkedMarked, MarkedK))))), true,
                "The marked vector space has one delta basis vector for each choice of a literal word and a wall mark."),
            MarkedNode("markedDelta", "Marked delta vectors", MarkedFieldAB(MarkedAll("x", MarkedMarked,
                MarkedEq(MarkedCall("markedDelta", MarkedK, MarkedX), MarkedCall("single", MarkedX, D(1))))), true,
                "The coefficient is one at the indicated marked word and zero at all other labels."),
            MarkedNode("Q", "Forgetting the mark", MarkedFieldAB(MarkedEq(MarkedOp("Q"),
                MarkedCall("lmapDomain", MarkedK, MarkedK, MarkedLambda("x", MarkedMarked, MarkedWord(MarkedX))))), true,
                "Linear pushforward sends each marked delta vector to the delta vector of its underlying literal word."),
            MarkedNode("S", "Summing the two marked lifts", MarkedSFormula(), true,
                "LinearCombination extends the displayed basis images linearly. The sum is over the subtype of wall positions, so each literal word has precisely two summands."),
            MarkedNode("Jstar", "The linear mark exchange", MarkedFieldAB(MarkedEq(MarkedOp("Jstar"),
                MarkedCall("lmapDomain", MarkedK, MarkedK, MarkedLambda("x", MarkedMarked, MarkedCall("J", MarkedX))))), true,
                "The map pushes basis labels forward under the exchange of marks."),
            MarkedNode("markedTranslation", "Linear translation on the cover", MarkedFieldAB(MarkedAll("t", MarkedSites,
                MarkedEq(MarkedCall("markedTranslation", MarkedK, MarkedT), MarkedCall("lmapDomain", MarkedK, MarkedK, MarkedCall("markedRotate", MarkedT))))), true,
                "Translation permutes the marked basis labels."),
            MarkedNode("markedU", "The one-site marked shift", MarkedFieldAB(MarkedEq(MarkedOp("markedU"),
                MarkedCall("markedTranslation", MarkedK, D(1)))), true,
                "This is the right shift by one site on the marked cover."),
            MarkedNode("marked_descent", "A free double cover and the descent identities", MarkedDescentFormula(), false,
                "The other wall of the other wall is the original mark, and the two marks are distinct. Translation preserves this unique pairing. On a marked delta vector, S after Q sums that vector and the vector with the other mark. On a literal delta vector, Q after S adds that vector twice. Translation sends the two marked lifts bijectively to the two lifts of the translated word; this gives the two intertwining identities for every displacement and hence for the one-site shifts. These identities hold over every field, including characteristic two."),
            MarkedNode("Coordinates", "The two ordered binary arcs", MarkedCoordinatesFormula(), true,
                "The dependent tuple consists of p,m,n,u,v. The first binary word has length m, the second has length n, and their numbers of true entries add to b. The proof fields are the length and filling equalities; no positivity is imposed on either arc."),
            MarkedNode("encode", "Placing the two arcs on the cycle", MarkedEncodeFormula(), true,
                "Starting at p, place wall,u,wall,v at consecutive offsets. The displayed piecewise expression reads the unique residue d in [0,L). The two wall offsets and the two interior intervals partition all positions, including when either interval is empty. Reindexing the counts gives a ones, b twos and two walls."),
            MarkedNode("decode", "Reading the arcs from a marked word", MarkedDecodeFormula(), true,
                "The nonzero residue of otherWall(x)−mark(x) has representative d between 1 and L−1. Its predecessor is m; the complementary nonwall length is n. The arcs contain no walls, so equality with letter two recovers their Boolean entries. Reconstructing every site also recovers the total number b of true entries."),
            MarkedNode("coordinateEquiv", "The marked-word coordinate equivalence", MarkedAB(
                MarkedAnd(MarkedEq(MarkedCall("forward", MarkedCall("coordinateEquiv", MarkedA, MarkedB)),
                        MarkedLambda("c", MarkedCoords, MarkedEnc(MarkedC))),
                    MarkedEq(MarkedCall("inverse", MarkedCall("coordinateEquiv", MarkedA, MarkedB)),
                        MarkedLambda("x", MarkedMarked, MarkedCall("decode", MarkedX))))), true,
                "Encoding and decoding are mutually inverse; the forward map is encode and the inverse map is decode."),
            MarkedNode("coordinateSwap", "Mark exchange in arc coordinates", MarkedAB(MarkedAll("c", MarkedCoords,
                MarkedEq(MarkedSwap(MarkedC), MarkedTuple(MarkedAdd(MarkedCP, MarkedCast(MarkedAdd(MarkedCM, D(1)))), MarkedCN, MarkedCM, MarkedCV, MarkedCU)))), true,
                "The second wall becomes the starting position, the two lengths exchange places, and the two binary words exchange places. The length and filling certificates follow by commutativity of addition."),
            MarkedNode("coordinateRotate", "Rotation acts only on the position", MarkedAB(MarkedAll("t", MarkedSites, MarkedAll("c", MarkedCoords,
                MarkedEq(MarkedRot(MarkedT, MarkedC), MarkedTuple(MarkedAdd(MarkedCP, MarkedT), MarkedCM, MarkedCN, MarkedCU, MarkedCV))))), true,
                "Both lengths and both binary words are retained; only p changes to p+t."),
            MarkedNode("marked_coordinates", "Round trips, layouts and coordinate symmetries", MarkedCoordinateTheorem(), false,
                "The representative of the distance to the other wall determines the first arc length uniquely. Reading and replacing all sites gives both inverse laws. Exchanging the two arcs shifts the starting position by m+1; after the second exchange the displacement is L and therefore zero. The two marks differ, which proves freeness in coordinates. Translation changes only the starting position and commutes with this exchange. All quantifiers include m=0, n=0 and a=b=0.")];

    private static DocumentBlock.Describe MarkedNode(string name, string title, Formula formula,
        bool definition, string prose) => Describe.Lean(
            DescribeId.Create("two-wall-marked-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/TwoWallWords." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula MarkedCall(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula MarkedAt(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula MarkedParenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula MarkedAll(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        type is Formula.TypeArrow ? MarkedParenthesized(type) : type, body);
    private static Formula MarkedEq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula MarkedNe(Formula x, Formula y) => Seq(Neg, MarkedParenthesized(MarkedEq(x, y)));
    private static Formula MarkedAnd(Formula x, Formula y) => new Formula.Logic(
        MarkedParenthesized(x), FormulaLogicOperator.And, MarkedParenthesized(y));
    private static Formula MarkedOr(Formula x, Formula y) => new Formula.Logic(
        MarkedParenthesized(x), FormulaLogicOperator.Or, MarkedParenthesized(y));
    private static Formula MarkedImp(Formula x, Formula y) => new Formula.Logic(
        MarkedParenthesized(x), FormulaLogicOperator.Implies, MarkedParenthesized(y));
    private static Formula MarkedAdd(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula MarkedSub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula MarkedPair(Formula x, Formula y) => MarkedTuple(x, y);
    private static Formula MarkedTuple(params Formula[] items) => MarkedParenthesized(Seq(
        items.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()));
    private static Formula MarkedCast(Formula x) => MarkedCall("natCast", MarkedParenthesized(x));
    private static Formula MarkedFin(Formula x) => MarkedCall("Fin", x);
    private static Formula MarkedBin(Formula x) => new Formula.TypeArrow(MarkedFin(x), MarkedBool);
    private static Formula MarkedAssumption(Formula x, Formula body) => Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula MarkedAB(Formula body) => MarkedAll("a", MarkedNats, MarkedAll("b", MarkedNats, body));
    private static Formula MarkedFieldAB(Formula body) => MarkedAll("K", MarkedCall("Type"), MarkedAssumption(MarkedCall("Field", MarkedK), MarkedAB(body)));
    private static Formula MarkedLambda(string name, Formula type, Formula body) =>
        MarkedParenthesized(Seq(MarkedParenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula MarkedSum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), InMacro, type)), Sp, MarkedParenthesized(body));
    private static Formula MarkedWord(Formula x) => MarkedCall("word", x);
    private static Formula MarkedMark(Formula x) => MarkedCall("mark", x);
    private static Formula MarkedLetterAt(Formula w, Formula p) => MarkedAt(MarkedCall("coe", w), p);
    private static Formula MarkedEnc(Formula c) => MarkedCall("encode", c);
    private static Formula MarkedSwap(Formula c) => MarkedCall("coordinateSwap", c);
    private static Formula MarkedRot(Formula t, Formula c) => MarkedCall("coordinateRotate", t, c);
    private static Formula MarkedOp(string name) => MarkedCall(name, MarkedK, MarkedA, MarkedB);
    private static Formula MarkedComp(Formula x, Formula y) => Seq(x, Sp, Circ, Sp, y);
    private static Formula MarkedSmul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula MarkedIdentity => MarkedCall("id");
    private static Formula MarkedEncAt(Formula p) => MarkedLetterAt(MarkedWord(MarkedEnc(MarkedC)), p);
    private static Formula MarkedRead(Formula w, Formula p) => MarkedCall("decide", MarkedEq(MarkedLetterAt(w, p), MarkedTwo));
    private static Formula MarkedBinaryLetter(Formula bit) => MarkedCall("ite", bit, MarkedTwo, MarkedOne);
    private static Formula MarkedBoth(params Formula[] clauses) => clauses.Aggregate((x, y) => MarkedAnd(x, y));

    private static Formula MarkedMarkedFormula() => MarkedAB(MarkedEq(MarkedMarked, MarkedCall("Subtype",
        MarkedLambda("x", MarkedCall("Prod", MarkedWords, MarkedSites), MarkedEq(MarkedLetterAt(MarkedCall("first", MarkedX), MarkedCall("second", MarkedX)), MarkedWall)))));

    private static Formula MarkedOtherFormula()
    {
        var q = F.Id("q"); var r = F.Id("r");
        var spec = MarkedLambda("q", MarkedSites, MarkedAnd(MarkedNe(q, MarkedMark(MarkedX)),
            MarkedAnd(MarkedEq(MarkedLetterAt(MarkedWord(MarkedX), q), MarkedWall), MarkedAll("r", MarkedSites,
                MarkedImp(MarkedEq(MarkedLetterAt(MarkedWord(MarkedX), r), MarkedWall), MarkedOr(MarkedEq(r, MarkedMark(MarkedX)), MarkedEq(r, q)))))));
        return MarkedAB(MarkedAll("x", MarkedMarked, MarkedEq(MarkedCall("otherWall", MarkedX), MarkedCall("Choose", spec))));
    }
    private static Formula MarkedMarkedRotateFormula() => MarkedAB(MarkedAll("t", MarkedSites, MarkedAll("x", MarkedMarked,
        MarkedAnd(MarkedEq(MarkedAt(MarkedCall("markedRotate", MarkedT), MarkedX), MarkedPair(MarkedAt(MarkedCall("rotate", MarkedT), MarkedWord(MarkedX)), MarkedAdd(MarkedMark(MarkedX), MarkedT))),
            MarkedEq(MarkedAt(MarkedCall("inverse", MarkedCall("markedRotate", MarkedT)), MarkedX),
                MarkedPair(MarkedAt(MarkedCall("inverse", MarkedCall("rotate", MarkedT)), MarkedWord(MarkedX)), MarkedSub(MarkedMark(MarkedX), MarkedT)))))));

    private static Formula MarkedSFormula()
    {
        var wallPositions = MarkedCall("Subtype", MarkedLambda("p", MarkedSites, MarkedEq(MarkedLetterAt(MarkedW, MarkedP), MarkedWall)));
        return MarkedFieldAB(MarkedEq(MarkedOp("S"), MarkedCall("linearCombination", MarkedK, MarkedLambda("w", MarkedWords,
            MarkedSum("p", wallPositions, MarkedCall("markedDelta", MarkedK, MarkedPair(MarkedW, MarkedCall("coe", MarkedP))))))));
    }
    private static Formula MarkedDescentFormula()
    {
        var involutive = MarkedAll("x", MarkedMarked, MarkedEq(MarkedCall("J", MarkedCall("J", MarkedX)), MarkedX));
        var free = MarkedAll("x", MarkedMarked, MarkedNe(MarkedCall("J", MarkedX), MarkedX));
        var equivariant = MarkedAll("t", MarkedSites, MarkedAll("x", MarkedMarked,
            MarkedEq(MarkedAt(MarkedCall("markedRotate", MarkedT), MarkedCall("J", MarkedX)), MarkedCall("J", MarkedAt(MarkedCall("markedRotate", MarkedT), MarkedX)))));
        var qs = MarkedEq(MarkedComp(MarkedOp("Q"), MarkedOp("S")), MarkedSmul(MarkedCall("scalar", MarkedK, D(2)), MarkedIdentity));
        var sq = MarkedEq(MarkedComp(MarkedOp("S"), MarkedOp("Q")), MarkedAdd(MarkedIdentity, MarkedOp("Jstar")));
        var rs = MarkedAll("t", MarkedSites, MarkedEq(MarkedComp(MarkedCall("markedTranslation", MarkedK, MarkedT), MarkedOp("S")),
            MarkedComp(MarkedOp("S"), MarkedCall("translation", MarkedK, MarkedT))));
        var qr = MarkedAll("t", MarkedSites, MarkedEq(MarkedComp(MarkedOp("Q"), MarkedCall("markedTranslation", MarkedK, MarkedT)),
            MarkedComp(MarkedCall("translation", MarkedK, MarkedT), MarkedOp("Q"))));
        var us = MarkedEq(MarkedComp(MarkedOp("markedU"), MarkedOp("S")), MarkedComp(MarkedOp("S"), MarkedOp("U")));
        var qu = MarkedEq(MarkedComp(MarkedOp("Q"), MarkedOp("markedU")), MarkedComp(MarkedOp("U"), MarkedOp("Q")));
        return MarkedFieldAB(MarkedBoth(involutive, free, equivariant, qs, sq, rs, qr, us, qu));
    }
    private static Formula MarkedCoordinatesFormula()
    {
        var m = F.Id("m"); var n = F.Id("n");
        var fields = MarkedCall("Sigma", MarkedSites, MarkedLambda("p", MarkedSites,
            MarkedCall("Sigma", MarkedNats, MarkedLambda("m", MarkedNats,
                MarkedCall("Sigma", MarkedNats, MarkedLambda("n", MarkedNats, MarkedCall("Prod", MarkedBin(m), MarkedBin(n))))))));
        return MarkedAB(MarkedEq(MarkedCoords, MarkedCall("Subtype", MarkedLambda("c", fields,
            MarkedAnd(MarkedEq(MarkedAdd(MarkedCM, MarkedCN), MarkedAdd(MarkedA, MarkedB)), MarkedEq(MarkedAdd(MarkedCall("ones", MarkedCU), MarkedCall("ones", MarkedCV)), MarkedB))))));
    }
    private static Formula MarkedEncodeFormula()
    {
        var q = F.Id("q"); var d = F.Id("d");
        var dDef = MarkedCall("val", MarkedSub(q, MarkedCP));
        var body = MarkedCall("ite", MarkedOr(MarkedEq(d, D(0)), MarkedEq(d, MarkedAdd(MarkedCM, D(1)))), MarkedWall,
            MarkedCall("ite", new Formula.Relation(d, FormulaRelationOperator.LessThanOrEqual, MarkedCM),
                MarkedBinaryLetter(MarkedAt(MarkedCU, MarkedCall("finIndex", MarkedSub(d, D(1))))),
                MarkedBinaryLetter(MarkedAt(MarkedCV, MarkedCall("finIndex", MarkedSub(MarkedSub(d, MarkedCM), D(2)))))));
        return MarkedAB(MarkedAll("c", MarkedCoords, MarkedAnd(MarkedEq(MarkedMark(MarkedEnc(MarkedC)), MarkedCP),
            MarkedAll("q", MarkedSites, MarkedAll("d", MarkedNats, MarkedImp(MarkedEq(d, dDef), MarkedEq(MarkedEncAt(q), body)))))));
    }
    private static Formula MarkedDecodeFormula()
    {
        var d = F.Id("d"); var m = MarkedSub(d, D(1)); var n = MarkedSub(MarkedAdd(MarkedA, MarkedB), MarkedParenthesized(m));
        var mark = MarkedMark(MarkedX); var word = MarkedWord(MarkedX);
        var u = MarkedLambda("i", MarkedFin(m), MarkedRead(word, MarkedAdd(mark, MarkedCast(MarkedAdd(MarkedCall("val", MarkedI), D(1))))));
        var v = MarkedLambda("i", MarkedFin(n), MarkedRead(word, MarkedAdd(mark, MarkedCast(MarkedAdd(MarkedAdd(MarkedParenthesized(m), D(2)), MarkedCall("val", MarkedI))))));
        return MarkedAB(MarkedAll("x", MarkedMarked, MarkedAll("d", MarkedNats,
            MarkedImp(MarkedEq(d, MarkedCall("val", MarkedSub(MarkedCall("otherWall", MarkedX), mark))),
                MarkedEq(MarkedCall("decode", MarkedX), MarkedTuple(mark, m, n, u, v))))));
    }
    private static Formula MarkedCoordinateTheorem()
    {
        var left = MarkedAll("c", MarkedCoords, MarkedEq(MarkedCall("decode", MarkedEnc(MarkedC)), MarkedC));
        var right = MarkedAll("x", MarkedMarked, MarkedEq(MarkedEnc(MarkedCall("decode", MarkedX)), MarkedX));
        var bounds = MarkedAll("c", MarkedCoords,
            MarkedAnd(new Formula.Relation(MarkedCM, FormulaRelationOperator.LessThan, MarkedAdd(MarkedAdd(MarkedA, MarkedB), D(1))),
                MarkedEq(MarkedCN, MarkedSub(MarkedAdd(MarkedA, MarkedB), MarkedCM))));
        var layout = MarkedAll("c", MarkedCoords, MarkedBoth(MarkedEq(MarkedEncAt(MarkedCP), MarkedWall),
            MarkedEq(MarkedEncAt(MarkedAdd(MarkedCP, MarkedCast(MarkedAdd(MarkedCM, D(1))))), MarkedWall),
            MarkedAll("i", MarkedFin(MarkedCM), MarkedEq(MarkedEncAt(MarkedAdd(MarkedCP, MarkedCast(MarkedAdd(MarkedCall("val", MarkedI), D(1))))), MarkedBinaryLetter(MarkedAt(MarkedCU, MarkedI)))),
            MarkedAll("i", MarkedFin(MarkedCN), MarkedEq(MarkedEncAt(MarkedAdd(MarkedCP, MarkedCast(MarkedAdd(MarkedAdd(MarkedCM, D(2)), MarkedCall("val", MarkedI))))), MarkedBinaryLetter(MarkedAt(MarkedCV, MarkedI))))));
        var swap = MarkedAll("c", MarkedCoords, MarkedEq(MarkedEnc(MarkedSwap(MarkedC)), MarkedCall("J", MarkedEnc(MarkedC))));
        var involutive = MarkedAll("c", MarkedCoords, MarkedEq(MarkedSwap(MarkedSwap(MarkedC)), MarkedC));
        var free = MarkedAll("c", MarkedCoords, MarkedNe(MarkedSwap(MarkedC), MarkedC));
        var rotation = MarkedAll("t", MarkedSites, MarkedAll("c", MarkedCoords, MarkedEq(MarkedEnc(MarkedRot(MarkedT, MarkedC)), MarkedAt(MarkedCall("markedRotate", MarkedT), MarkedEnc(MarkedC)))));
        var commute = MarkedAll("t", MarkedSites, MarkedAll("c", MarkedCoords, MarkedEq(MarkedRot(MarkedT, MarkedSwap(MarkedC)), MarkedSwap(MarkedRot(MarkedT, MarkedC)))));
        return MarkedAB(MarkedBoth(left, right, bounds, layout, swap, involutive, free, rotation, commute));
    }
}
