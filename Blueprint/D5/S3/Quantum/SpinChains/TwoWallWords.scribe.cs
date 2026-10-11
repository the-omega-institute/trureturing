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
        Blocks(
            Paragraph(Text("Let a and b be natural numbers and L = a+b+2. The positions form ZMod(L). The letters one, two and wall denote the physical letters 1, 2 and 3, respectively; their Fin(3) encodings are 0, 1 and 2. Words retain their positions and are not identified under rotation. The vector space over any field K consists of finite linear combinations of counted words. Its delta vector at w has coefficient one at w and zero elsewhere. Endomorphism multiplication means composition, with the right factor acting first.")),
            Node("Letter", "The three-letter type", Eq(Letter, Call("Fin", D(3))), true,
                "The letter type has exactly three elements."),
            Node("one", "Letter one", Eq(Call("one"), D(0)), true, "The first encoding denotes letter 1."),
            Node("two", "Letter two", Eq(Call("two"), D(1)), true, "The second encoding denotes letter 2."),
            Node("wall", "The wall", Eq(Call("wall"), D(2)), true, "The third encoding denotes the wall 3."),
            Node("Pos", "Cyclic positions", AB(Eq(Sites, Call("ZMod", Length))), true,
                "Addition of positions is taken modulo L, so the last and first positions are adjacent."),
            Node("lengthNeZero", "Positive cyclic length", AB(Eq(Call("lengthNeZero", A, B),
                Call("NeZeroMk", Call("proofOf", Not(Eq(Length, D(0))))))), true,
                "The sum a+b+2 is nonzero. NeZeroMk packages this proof and supplies the finite enumeration of cyclic positions."),
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
                "A swap is a permutation of sites, so finite-sum reindexing preserves every count. Translation carries the bond at p to the bond at p+t, with the same oriented input test and exchanged output. Reindexing the complete bond sum therefore gives commutation. Repeated right shifts add their displacements in ZMod(L); displacement L is zero. The coupling formula inherits commutation by linearity.")),
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
    private static Formula Not(Formula x) => Seq(Neg, Parenthesized(x));
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
}
