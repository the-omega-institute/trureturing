using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class SeparatorGapActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/SeparatorGapAction.";
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string n, Formula t) =>
        new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] bs) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], f);
    private static Formula Fn(Formula a, Formula b) => Call("Function", a, b);
    private static Formula At(Formula f, Formula a) => Call("apply", f, a);
    private static Formula Typed(Formula a, Formula b) => Seq(a, Colon, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula SeqType => Fn(I("Int"), I("E"));
    private static Formula Labels(string n) => At(I("I"), I(n));
    private static Formula Perm(string n) => Call("Perm", Labels(n));
    private static Formula Len(string n) => At(I("d"), I(n));
    private static Formula Data(string n, Formula i, Formula j) =>
        Call("data", I("F"), I(n), i, j);
    private static Formula Sep => Call("separator", I("F"));
    private static Formula Rep(string n, Formula sigma, Formula x) =>
        Call("replace", I("F"), I(n), sigma, x);
    private static Formula Sel(string n, Formula x, Formula i) =>
        Call("Selected", I("F"), I(n), x, I("s"), i);
    private static Formula Offset => Add(Add(I("s"), Num(1)), Call("integerIndex", I("j")));
    private static Formula Radius => Add(Len("n"), Num(1));
    private static Formula FamilyType => Call("Family", I("E"), I("I"), I("d"));
    private static Formula Base(Formula f, params Formula.BoundVariable[] extra) => All(f,
        [B("E", I("Type")), B("I", Fn(I("Nat"), I("Type"))),
         B("d", Fn(I("Nat"), I("Nat"))), B("F", FamilyType), .. extra]);
    private static Formula GraphScope(Formula f, bool topology, bool finite,
        params Formula.BoundVariable[] extra)
    {
        Formula bracket(string name, Formula t) => Seq(OpenBracket, Call(name, t), CloseBracket, Sp);
        if (finite)
            f = Seq(bracket("Fintype", I("V")), bracket("Fintype", I("E")),
                bracket("DecidableEq", I("V")), f);
        if (topology)
            f = Seq(bracket("TopologicalSpace", I("E")), bracket("DiscreteTopology", I("E")), f);
        return Base(f, [B("V", I("Type")),
            B("G", Call("DirectedMultigraph", I("V"), I("E"))),
            B("P", Call("Paths", I("F"), I("G"))), .. extra]);
    }
    private static Formula Act => Call("finiteAction", I("F"), I("G"), I("P"));
    private static Formula Image(Formula g, Formula x) => Call("historyEdges", At(At(Act, g), x));

    public DocumentDefinition Create()
    {
        var entries = new List<DocumentBlock>();
        void Entry(string name, string title, Formula f, string prose, bool definition = false) =>
            entries.Add(Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
                DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(f)),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
                definition ? DescribeRole.Definition : DescribeRole.Theorem));
        Entry("Family", "One separator and a family of data lengths",
            All(Typed(FamilyType, I("Type")), B("E", I("Type")),
                B("I", Fn(I("Nat"), I("Type"))), B("d", Fn(I("Nat"), I("Nat")))),
            "Family stores a separator b, positive injectively indexed lengths d(n), and "
            + "injective codes I(n)→Fin(d(n))→E avoiding b at every offset. E and I may "
            + "have independent universes. No invariant-selection or action law is a premise.", true);
        Entry("Selected", "A complete separator-bounded code word",
            Base(Iff(Sel("n", I("x"), I("i")),
                And(Equal(At(I("x"), I("s")), Sep),
                    And(Equal(At(I("x"), Add(Add(I("s"), Len("n")), Num(1))), Sep),
                        All(Equal(At(I("x"), Offset), Data("n", I("i"), I("j"))),
                            B("j", Call("Fin", Len("n"))))))),
                B("n", I("Nat")), B("x", SeqType), B("s", I("Int")), B("i", Labels("n"))),
            "All natural coordinates in integer sums are cast to Int. Separator avoidance "
            + "makes the two endpoints consecutive separator positions. The sequence may "
            + "contain arbitrary noncoded gaps, extra edge symbols, and infinite separator-free tails.", true);
        Entry("replace", "Simultaneous replacement of all eligible gaps of one length",
            Base(Typed(At(Rep("n", I("sigma"), I("x")), I("t")), I("E")),
                B("n", I("Nat")), B("sigma", Perm("n")), B("x", SeqType), B("t", I("Int"))),
            "An interior hit outputs data(n,sigma(i),j), and every other coordinate returns x(t). "
            + "Two overlapping interiors between consecutive separators must have identical "
            + "endpoints. Length injectivity, code injectivity and the offset equation give "
            + "uniqueness, so the chosen hit does not change the output.", true);
        Entry("separator_iff", "Exact preservation of the entire separator set",
            Base(Iff(Equal(At(Rep("n", I("sigma"), I("x")), I("t")), Sep),
                Equal(At(I("x"), I("t")), Sep)), B("n", I("Nat")), B("sigma", Perm("n")),
                B("x", SeqType), B("t", I("Int"))),
            "At a hit, both the old and new data avoid b. Off hits the coordinate is fixed. "
            + "Thus neither a new separator nor a missing separator can alter the parsing.");
        Entry("selected_same", "Eligibility is invariant in both directions",
            Base(Iff(Sel("n", Rep("n", I("sigma"), I("x")), At(I("sigma"), I("i"))),
                Sel("n", I("x"), I("i"))), B("n", I("Nat")), B("sigma", Perm("n")),
                B("x", SeqType), B("s", I("Int")), B("i", Labels("n"))),
            "An old selected interval is relabeled by sigma. Conversely, new selection "
            + "gives an old interval between the same consecutive separators. Any old hit "
            + "meeting its interior has those endpoints; if none exists, the entire data "
            + "word was unchanged and was already eligible. This does not assume an inverse law.");
        Entry("replace_on_other_gap", "Other lengths preserve every data edge",
            Base(Imp(Ne(I("n"), I("m")), Imp(Sel("m", I("x"), I("i")),
                Equal(At(Rep("n", I("sigma"), I("x")), Offset), At(I("x"), Offset)))),
                B("n", I("Nat")), B("m", I("Nat")), B("sigma", Perm("n")), B("x", SeqType),
                B("s", I("Int")), B("i", Labels("m")), B("j", Call("Fin", Len("m")))),
            "Different indexed lengths cannot have the same endpoints. Their selected "
            + "interiors are disjoint even when they share a separator.");
        Entry("selected_other", "Different lengths neither create nor remove a selection",
            Base(Imp(Ne(I("n"), I("m")), Iff(Sel("m", Rep("n", I("sigma"), I("x")), I("i")),
                Sel("m", I("x"), I("i")))), B("n", I("Nat")), B("m", I("Nat")),
                B("sigma", Perm("n")), B("x", SeqType), B("s", I("Int")), B("i", Labels("m"))),
            "Both directions follow from exact separator preservation and interval rigidity. "
            + "The converse covers gaps that were initially not code words.");
        Entry("replace_mul", "The actual noncommutative composition order",
            Base(Equal(Rep("n", I("sigma"), Rep("n", I("tau"), I("x"))),
                Rep("n", Mul(I("sigma"), I("tau")), I("x"))), B("n", I("Nat")),
                B("sigma", Perm("n")), B("tau", Perm("n")), B("x", SeqType)),
            "At a selected interval the label becomes sigma(tau(i)); off every interval "
            + "both maps fix the coordinate. Unit and both inverse laws follow.");
        Entry("replace_commute", "Commutation derived from spatial separation",
            Base(Imp(Ne(I("n"), I("m")), Equal(
                Rep("n", I("sigma"), Rep("m", I("tau"), I("x"))),
                Rep("m", I("tau"), Rep("n", I("sigma"), I("x"))))),
                B("n", I("Nat")), B("m", I("Nat")), B("sigma", Perm("n")),
                B("tau", Perm("m")), B("x", SeqType)),
            "The two rules preserve each other's selections and central data. This proves "
            + "commutation on every sequence, although both rules can move the same whole history.");
        Entry("replace_local", "A finite original-coordinate window",
            Base(Imp(All(Imp(Le(Sub(I("t"), Radius), I("s")),
                Imp(Le(I("s"), Add(I("t"), Radius)), Equal(At(I("x"), I("s")), At(I("y"), I("s"))))),
                B("s", I("Int"))), Equal(At(Rep("n", I("sigma"), I("x")), I("t")),
                At(Rep("n", I("sigma"), I("y")), I("t")))),
                B("n", I("Nat")), B("sigma", Perm("n")), B("x", SeqType), B("y", SeqType),
                B("t", I("Int"))),
            "Radius d(n)+1 contains both endpoints and all data of every hit at t. "
            + "Locality and integer-translation equivariance give continuity using the existing "
            + "historyWindow_continuous theorem for the finite discrete word space.");
        Entry("Paths", "Legal paths with distinct endpoint roles",
            Base(All(Typed(Call("Paths", I("F"), I("G")), I("Prop")), B("V", I("Type")),
                B("G", Call("DirectedMultigraph", I("V"), I("E"))))),
            "Each data word is legal, starts at target(b), and ends at source(b). "
            + "The separator need not be a loop. These are finite-edge conditions.", true);
        Entry("onHistory", "Replacement on all legal histories",
            GraphScope(Typed(Call("onHistory", I("F"), I("G"), I("P"), I("n"), I("sigma"), I("x")),
                Call("History", I("G"))), false, false, B("n", I("Nat")), B("sigma", Perm("n")),
                B("x", Call("History", I("G")))),
            "Interior seams use data legality. The first and last data edges meet the "
            + "unchanged separators through their actual target and source. All remaining seams "
            + "retain the original legal-history equation.", true);
        Entry("homeomorph", "A homeomorphism with its actual inverse",
            GraphScope(Typed(Call("homeomorph", I("F"), I("G"), I("P"), I("n"), I("sigma")),
                Call("Homeomorph", Call("History", I("G")), Call("History", I("G")))), true, false,
                B("n", I("Nat")), B("sigma", Perm("n"))),
            "The inverse uses sigma inverse on exactly the same intervals. Both maps are "
            + "continuous on the original legal subspace; no encoded-history restriction appears.", true);
        Entry("action", "A coordinate in the full unit-shift centralizer",
            GraphScope(Typed(Call("action", I("F"), I("G"), I("P"), I("n")),
                Call("MonoidHom", Perm("n"), Call("FullAut", I("G")))), true, false, B("n", I("Nat"))),
            "Translation of a selected word translates its start. Thus the homeomorphism "
            + "commutes with the actual unit shift, and its group law has ordinary composition order.", true);
        Entry("FinitePerm", "The noncommutative restricted product at identity",
            All(Typed(Call("FinitePerm", I("J")), I("Type")), B("J", Fn(I("Nat"), I("Type")))),
            "FinitePerm J is Mathlib RestrictedProduct of Perm(J(n)), with bottom subgroups "
            + "and the cofinite filter. Its elements have finitely many nonidentity coordinates. "
            + "Multiplication is coordinatewise and the individual factors may be nonabelian.", true);
        Entry("finiteAction", "All finitely many active coordinates act together",
            GraphScope(Typed(Act, Call("MonoidHom", Call("FinitePerm", I("I")),
                Call("FullAut", I("G")))), true, false),
            "Finite noncommProd assembles the coordinate homomorphisms. Cross-length "
            + "commutation proves independence of ordering and identity padding. Enlarging "
            + "two supports to their union proves the homomorphism law without commuting "
            + "the two factors inside a single coordinate. Every tuple has a finite window "
            + "as a finite composition. No unrestricted infinite-product continuity is claimed.", true);
        Entry("finiteAction_mem", "Subgroup closure of the simultaneous action",
            GraphScope(Imp(All(Call("member", Call("action", I("F"), I("G"), I("P"), I("n"),
                At(I("g"), I("n"))), I("H")), B("n", I("Nat"))),
                Call("member", At(Act, I("g")), I("H"))), true, false,
                B("H", Call("Subgroup", Call("FullAut", I("G")))), B("g", Call("FinitePerm", I("I")))),
            "The finite fold stays in any subgroup containing all coordinate images. "
            + "This is used to place the alternating product in the original representation kernel.");
        Entry("finiteAction_at_selected", "Joint coordinate observation on arbitrary tails",
            GraphScope(Imp(Sel("n", Call("historyEdges", I("x")), I("i")),
                Equal(At(Image(I("g"), I("x")), Offset),
                    Data("n", At(At(I("g"), I("n")), I("i")), I("j")))), true, false,
                B("g", Call("FinitePerm", I("I"))), B("x", Call("History", I("G"))),
                B("n", I("Nat")), B("s", I("Int")), B("i", Labels("n")), B("j", Call("Fin", Len("n")))),
            "On a selected n-gap the complete finite-support action outputs D(n,g(n)(i)) "
            + "at every offset. Every other length leaves this observation fixed regardless "
            + "of how its action changes the exterior history.");
        Entry("finiteAction_injective", "Joint faithfulness of the countable finite-support action",
            GraphScope(Imp(Call("Essential", I("G")), Call("FunctionInjective", Act)), true, true),
            "The legal word b D(n,i) b has positive length and is realized by an actual "
            + "bilateral history using EssentialWordRealization.exists_history_containing. "
            + "Comparing two actions on these witnesses determines every data word, hence "
            + "every permutation coordinate. The action itself remains defined on all histories.");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Length-separated separator actions on bilateral legal histories.", H("Separator gaps"),
            Blocks(entries.ToArray())));
    }
}
