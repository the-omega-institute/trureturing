using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class PyranimPositionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Games/PyranimPosition";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Asymptotics/binyaminkniffen2026pyranim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable positions and legal options in Pyranim",
        H("Stable positions and legal options in Pyranim"),
        Blocks(
            Node("Interval", "Nonempty intervals",
                IntervalBody(),
                "The nonempty chips of width n have endpoints l and r with 1 ≤ l ≤ r ≤ n. Their order is interval inclusion.",
                DescribeRole.Definition, true),
            Node("Stable", "All stable positions",
                StableBody(),
                "A position contains every subinterval of each surviving chip. The board may have absent bottom chips, including the empty board.",
                DescribeRole.Definition, true),
            Node("emptyStable", "Empty position",
                All("n", Nat, Eq(Val(Call("emptyStable", V("n"))), Emptyset)),
                "No chip survives in the empty stable position.",
                DescribeRole.Definition),
            Node("stableEquivDyck", "Stable positions and Dyck words",
                All("n", Nat, Seq(Call("stableEquivDyck", V("n")), Colon, Equiv(Stable(V("n")), Paths(Add(V("n"), D(1)))))),
                "The maximal omitted start in each column gives a bounded nondecreasing inversion sequence. The inverse keeps intervals whose start exceeds that threshold. The frozen inversion-sequence equivalence gives the Dyck word.",
                DescribeRole.Definition),
            Node("stableCard", "Catalan count",
                All("n", Nat, Eq(Card(Stable(V("n"))), Call("catalan", Add(V("n"), D(1))))),
                "The Catalan count uses Dyck semilength n+1, including width zero.",
                DescribeRole.Theorem, true),
            Node("FullBottom", "Full bottom row",
                All("n", Nat, Eq(Call("FullBottom", V("n")), SetOf("I", Stable(V("n")), All("c", Chip, Imp(Eq(Left(V("c")), Right(V("c"))), In(V("c"), Val(V("I")))))))),
                "Every singleton interval belongs to a full-bottom position.",
                DescribeRole.Definition),
            Node("raiseRight", "Lengthening the right endpoint",
                All("n", Nat, All("c", Chip, EndpointPair(Call("raiseRight", V("c")), Left(V("c")), Add(Right(V("c")), D(1))))),
                "The width and the right endpoint increase by one.",
                DescribeRole.Definition),
            Node("lowerRight", "Shortening a nonsingleton",
                All("n", Nat, All("c", Call("Interval", Add(V("n"), D(1))), TypedAll("h", Lt(Left(V("c")), Right(V("c"))), EndpointPair(Call("lowerRight", V("c"), V("h")), Left(V("c")), Subtract(Right(V("c")), D(1)))))),
                "The width and the right endpoint decrease by one. The strict endpoint inequality supplies the proof h that shortening leaves a nonempty interval.",
                DescribeRole.Definition),
            Node("raiseRight_lowerRight", "Recovering a nonsingleton",
                All("n", Nat, All("c", Call("Interval", Add(V("n"), D(1))), TypedAll("h", Lt(Left(V("c")), Right(V("c"))), Eq(Call("raiseRight", Call("lowerRight", V("c"), V("h"))), V("c"))))),
                "Lengthening recovers the original nonsingleton.",
                DescribeRole.Lemma),
            Node("removeBottom", "Removing the full bottom row",
                All("n", Nat, All("I", Call("FullBottom", Add(V("n"), D(1))), Eq(Val(Call("removeBottom", V("I"))), SetOf("c", Chip, In(Call("raiseRight", V("c")), Val(Val(V("I")))))))),
                "The surviving chips have right endpoints shifted down by one.",
                DescribeRole.Definition),
            Node("fullBottomSuccEquiv", "Full-bottom positions as smaller boards",
                All("n", Nat, Seq(Call("fullBottomSuccEquiv", V("n")), Colon, Equiv(Call("FullBottom", Add(V("n"), D(1))), Stable(V("n"))))),
                "Deleting the bottom row and reinstating it give inverse maps.",
                DescribeRole.Definition),
            Node("stabilize", "Largest stable subposition",
                All("n", Nat, All("S", Call("Set", Chip), Eq(Val(Call("stabilize", V("S"))), SetOf("b", Chip, All("a", Chip, Imp(Le(V("a"), V("b")), In(V("a"), V("S")))))))),
                "A surviving chip remains stable exactly when all its subintervals are in the supplied set.",
                DescribeRole.Definition, true),
            Node("removeChip", "Chip removal and cascade",
                All("n", Nat, All("I", Stable(V("n")), All("c", Chip, Eq(Val(Call("removeChip", V("I"), V("c"))), SetOf("b", Chip, And(In(V("b"), Val(V("I"))), Not(Le(V("c"), V("b"))))))))),
                "Remove the selected chip and every surviving superinterval that it supports.",
                DescribeRole.Definition, true),
            Node("removeChip_eq_stabilize", "Cascade agrees with stabilization",
                All("n", Nat, All("I", Stable(V("n")), All("c", Chip, Eq(Call("removeChip", V("I"), V("c")), Call("stabilize", Seq(Val(V("I")), Setminus, Sp, SetOf("z", Chip, Eq(V("z"), V("c"))))))))),
                "The ideal obtained by removing all superintervals is the largest ideal after deleting the selected chip.",
                DescribeRole.Lemma, true),
            Node("LeftAbove", "Immediate upper left chip",
                Above("LeftAbove", And(Eq(Add(Left(V("u")), D(1)), Left(V("c"))), Eq(Right(V("u")), Right(V("c"))))),
                "The immediate upper left chip extends the left endpoint by one.",
                DescribeRole.Definition, true),
            Node("RightAbove", "Immediate upper right chip",
                Above("RightAbove", And(Eq(Left(V("u")), Left(V("c"))), Eq(Add(Right(V("c")), D(1)), Right(V("u"))))),
                "The immediate upper right chip extends the right endpoint by one.",
                DescribeRole.Definition, true),
            Node("ImmediateAbove", "Immediate support step",
                Above("ImmediateAbove", Or(Call("LeftAbove", V("c"), V("u")), Call("RightAbove", V("c"), V("u")))),
                "A support step extends exactly one endpoint to its immediate neighbor.",
                DescribeRole.Definition, true),
            Node("cascade_iff", "Cascade along support paths",
                All("n", Nat, All("I", Stable(V("n")), Chips(Iff(In(V("u"), Val(Call("removeChip", V("I"), V("c")))), And(In(V("u"), Val(V("I"))), Not(Call("ReflTransGen", V("ImmediateAbove"), V("c"), V("u")))))))),
                "A reflexive support path includes the selected chip itself. Transitive support is equivalent to interval containment.",
                DescribeRole.Lemma, true),
            Node("Visible", "Visible surviving chip",
                All("n", Nat, All("I", Stable(V("n")), All("c", Chip, Iff(Call("Visible", V("I"), V("c")), And(In(V("c"), Val(V("I"))), Not(And(AboveIn("LeftAbove"), AboveIn("RightAbove")))))))),
                "A surviving chip is legal to select when its two immediate upper neighbors are not both present.",
                DescribeRole.Definition, true),
            Node("UpperCover", "Cover within the surviving position",
                All("n", Nat, All("I", Stable(V("n")), Chips(Iff(Call("UpperCover", V("I"), V("c"), V("u")), And(In(V("u"), Val(V("I"))), And(Lt(V("c"), V("u")), All("v", Chip, Imp(In(V("v"), Val(V("I"))), Imp(Lt(V("c"), V("v")), Imp(Lt(V("v"), V("u")), V("False"))))))))))),
                "A cover is a surviving strict superinterval with no surviving chip strictly between the two.",
                DescribeRole.Definition),
            Node("visible_iff_covers", "Visibility from order covers",
                VisibleCovers(),
                "The only possible covers extend one endpoint by one. Visibility is therefore preserved by a survivor-poset order isomorphism.",
                DescribeRole.Lemma),
            Node("LegalOption", "Legal successor position",
                All("n", Nat, All("I", Stable(V("n")), All("J", Stable(V("n")), Iff(Call("LegalOption", V("I"), V("J")), Ex("c", Chip, And(Call("Visible", V("I"), V("c")), Eq(V("J"), Call("removeChip", V("I"), V("c"))))))))),
                "The option set consists of resulting stable positions reached by selecting a visible chip and applying the cascade.",
                DescribeRole.Definition, true),
            Node("Options", "Subtype of actual legal options",
                All("n", Nat, All("I", Stable(V("n")), Eq(Call("Options", V("I")), SetOf("J", Stable(V("n")), Call("LegalOption", V("I"), V("J")))))),
                "Each option is a stable position together with its legal-move property.",
                DescribeRole.Definition, true),
            Node("legalOption_ssubset", "A move strictly reduces the position",
                All("n", Nat, All("I", Stable(V("n")), All("J", Stable(V("n")), Imp(Call("LegalOption", V("I"), V("J")), Seq(Val(V("J")), Subset, Sp, Val(V("I"))))))),
                "The chip selected by a legal move witnesses strict inclusion of the surviving set.",
                DescribeRole.Lemma),
            Node("chipCount", "Surviving chips",
                All("n", Nat, All("I", Stable(V("n")), Eq(Call("chipCount", V("I")), App(Seq(Named("Finset"), Dot, Named("card")), Call("toFinset", Val(V("I"))))))),
                "The cardinality is finite because each chip has two bounded endpoints.",
                DescribeRole.Definition),
            Node("chipCount_lt_of_option", "Legal options lower chip count",
                All("n", Nat, All("I", Stable(V("n")), All("J", Stable(V("n")), Imp(Call("LegalOption", V("I"), V("J")), Lt(Call("chipCount", V("J")), Call("chipCount", V("I"))))))),
                "The strict inclusion of finite surviving sets gives the decrease.",
                DescribeRole.Lemma),
            Node("legalOption_wellFounded", "Well-founded legal descent",
                All("n", Nat, Call("WellFounded", Seq(LambdaLower, Sp, Par(Seq(V("J"), Colon, Stable(V("n")))), Sp, Par(Seq(V("I"), Colon, Stable(V("n")))), Mapsto, Call("LegalOption", V("I"), V("J"))))),
                "Chip count is a natural-number measure for legal descent.",
                DescribeRole.Lemma),
            Node("GameIso", "Recursive game isomorphism",
                IsoBody(),
                "At every pair of positions there must be a bijection of actual legal options whose matched positions are again game isomorphic. The first board’s chip count decreases in the recursion.",
                DescribeRole.Definition, true),
            Node("gameIso_iff", "Recursive equation for game isomorphism",
                IsoBody(),
                "Unfolding the recursion gives the option-bijection criterion at all widths.",
                DescribeRole.Lemma, true),
            Node("gameIso_refl", "Reflexive game isomorphism",
                All("n", Nat, All("I", Stable(V("n")), Iso(V("I"), V("I")))),
                "The identity bijection works at each pair of identical positions by well-founded induction.",
                DescribeRole.Lemma),
            Node("gameIso_symm", "Symmetric game isomorphism",
                BothPositions(Imp(Iso(V("I"), V("J")), Iso(V("J"), V("I")))),
                "Invert the option bijection at each step of well-founded induction.",
                DescribeRole.Lemma),
            Node("gameIso_trans", "Transitive game isomorphism",
                BothPositions(All("l", Nat, All("K", Stable(V("l")), Imp(Iso(V("I"), V("J")), Imp(Iso(V("J"), V("K")), Iso(V("I"), V("K"))))))),
                "Compose the two option bijections and use well-founded induction on their matched options.",
                DescribeRole.Lemma),
            Node("DyckAt", "Dyck words of fixed semilength",
                All("n", Nat, Eq(Call("DyckAt", V("n")), Paths(V("n")))),
                "The subtype records the number of up-steps, equal to the number of down-steps.",
                DescribeRole.Definition),
            Node("rankBlock", "Dyck block with a movable down-step",
                RankBlockBody(),
                "U and D are up-steps and down-steps. The index i places the first down-step after i+1 up-steps.",
                DescribeRole.Definition),
            Node("rankBlock_semilength", "Semilength of a rank block",
                All("L", Nat, All("i", RankIndex, Eq(Field(Block(V("i")), "semilength"), Add(V("L"), D(1))))),
                "Every choice of the moving step leaves L+1 up-steps and L+1 down-steps.",
                DescribeRole.Lemma),
            Node("rankBlock_length", "Length of a rank block",
                All("L", Nat, All("i", RankIndex, Eq(Field(Steps(Block(V("i"))), "length"), Multiply(D(2), Par(Add(V("L"), D(1))))))),
                "Every choice of i gives the same number of steps.",
                DescribeRole.Lemma),
            Node("exchangeDyck", "Replacing a balanced block",
                ExchangeBody(),
                "The original word is the prefix, the u block and the suffix. Equal lengths and matched up- and down-step counts make replacement by v preserve both the prefix inequalities and the ambient semilength.",
                DescribeRole.Definition),
            Node("rankBlock_strict", "Strict increase in chip count under block replacement",
                RankStrictBody(),
                "Increasing i weakly decreases every column’s omitted-start threshold and strictly enlarges the stable ideal. The other steps of the Dyck word are fixed.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("pyranim-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula V(string name) => F.Id(name);

    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));

    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);

    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);

    private static Formula Par(Formula f) => Seq(Open, f, Close);

    private static Formula Field(Formula x, string f) => Seq(x, Dot, V(f));

    private static Formula All(string x, Formula type, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, f);

    private static Formula Ex(string x, Formula type, Formula f) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, f);

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);

    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);

    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);

    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));

    private static Formula Not(Formula x) => Seq(Neg, Sp, Par(x));

    private static Formula SetOf(string x, Formula type, Formula f) => Seq(OpenBrace, V(x), Colon, type, Mid, Sp, f, CloseBrace);

    private static Formula Equiv(Formula a, Formula b) => Call("Equiv", a, b);

    private static Formula Val(Formula x) => Field(x, "val");

    private static Formula Card(Formula x) => App(Seq(Named("Nat"), Dot, Named("card")), x);

    private static Formula Stable(Formula n) => Call("Stable", n);

    private static Formula Iso(Formula a, Formula b) => Call("GameIso", a, b);

    private static Formula First(Formula p) => Seq(p, Dot, D(1));

    private static Formula Second(Formula p) => Seq(p, Dot, D(2));

    private static Formula Chip => Call("Interval", V("n"));

    private static Formula Left(Formula c) => Field(c, "left");

    private static Formula Right(Formula c) => Field(c, "right");

    private static Formula EndpointPair(Formula c, Formula l, Formula r) => And(Eq(Left(c), l), Eq(Right(c), r));

    private static Formula Chips(Formula f) => All("c", Chip, All("u", Chip, f));

    private static Formula TypedAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, type)), Comma, Sp, body);

    private static Formula Above(string name, Formula condition) =>
        All("n", Nat, Chips(Iff(Call(name, V("c"), V("u")), condition)));

    private static Formula AboveIn(string name) =>
        Ex("u", Chip, And(In(V("u"), Val(V("I"))), Call(name, V("c"), V("u"))));

    private static Formula IntervalBody()
    {
        var p = V("p"); var c = V("c"); var u = V("u");
        var endpoints = SetOf("p", Seq(Nat, Times, Sp, Nat), And(Le(D(1), First(p)),
            And(Le(First(p), Second(p)), Le(Second(p), V("n")))));
        var order = Chips(Iff(Le(c, u), And(Le(Left(u), Left(c)), Le(Right(c), Right(u)))));
        return All("n", Nat, And(Equiv(Chip, endpoints), order));
    }

    private static Formula StableBody() =>
        All("n", Nat, Eq(Stable(V("n")), SetOf("S", Call("Set", Chip),
            Call("IsLowerSet", V("S")))));

    private static Formula Paths(Formula n) =>
        SetOf("w", V("DyckWord"), Eq(Field(V("w"), "semilength"), n));

    private static Formula VisibleCovers()
    {
        var c = V("c"); var i = V("I");
        var pair = Ex("u", Chip, Ex("v", Chip, And(Call("UpperCover", i, c, V("u")),
            And(Call("UpperCover", i, c, V("v")), Ne(V("u"), V("v"))))));
        return All("n", Nat, All("I", Stable(V("n")), All("c", Chip,
            Iff(Call("Visible", i, c), And(In(c, Val(i)), Not(pair))))));
    }

    private static Formula BothPositions(Formula f) =>
        All("n", Nat, All("m", Nat, All("I", Stable(V("n")), All("J", Stable(V("m")), f))));

    private static Formula IsoBody()
    {
        var a = V("a"); var i = V("I"); var j = V("J");
        return BothPositions(Iff(Iso(i, j), Ex("e", Equiv(Call("Options", i), Call("Options", j)),
            All("a", Call("Options", i), Iso(Val(a), Val(App(V("e"), a)))))));
    }

    private static Formula RankIndex => Call("Fin", Add(V("L"), D(1)));

    private static Formula Block(Formula i) => Call("rankBlock", V("L"), i);

    private static Formula Steps(Formula p) => Field(p, "toList");

    private static Formula Append(params Formula[] lists)
    {
        var items = new System.Collections.Generic.List<Formula> { lists[0] };
        foreach (var list in lists[1..])
        {
            items.Add(Plus);
            items.Add(Plus);
            items.Add(list);
        }
        return Seq([.. items]);
    }

    private static Formula RankBlockBody()
    {
        var i = Val(V("i"));
        var steps = Append(Call("replicate", Add(i, D(1)), V("U")), Seq(OpenBracket, V("D"), CloseBracket),
            Call("replicate", Subtract(V("L"), i), V("U")), Call("replicate", V("L"), V("D")));
        return All("L", Nat, All("i", RankIndex, Eq(Steps(Block(V("i"))), steps)));
    }

    private static Formula ListSteps => Call("List", V("DyckStep"));

    private static Formula FixedWidthPaths => Call("DyckAt", Add(V("n"), D(1)));

    private static Formula Split(Formula w, Formula block) =>
        Eq(Steps(Val(w)), Append(V("pre"), Steps(block), V("post")));

    private static Formula ExchangeBody()
    {
        var u = V("u"); var v = V("v"); var w = V("w");
        var sameSemilength = Eq(Field(u, "semilength"), Field(v, "semilength"));
        var result = Split(Call("exchangeDyck", w, V("pre"), V("post"), u, v, V("h"), V("s")), v);
        return All("n", Nat, All("w", FixedWidthPaths, All("pre", ListSteps, All("post", ListSteps,
            All("u", V("DyckWord"), All("v", V("DyckWord"), TypedAll("h", Split(w, u),
                TypedAll("s", sameSemilength, result))))))));
    }

    private static Formula RankStrictBody()
    {
        var e = Call("stableEquivDyck", V("n"));
        Formula Rank(string w) => Call("chipCount", App(Field(e, "symm"), V(w)));
        return All("n", Nat, All("L", Nat, All("i", RankIndex, All("j", RankIndex,
            Imp(Lt(V("i"), V("j")), All("p", FixedWidthPaths, All("q", FixedWidthPaths,
                All("pre", ListSteps, All("post", ListSteps, Imp(Split(V("p"), Block(V("i"))),
                    Imp(Split(V("q"), Block(V("j"))), Lt(Rank("p"), Rank("q")))))))))))));
    }
}
