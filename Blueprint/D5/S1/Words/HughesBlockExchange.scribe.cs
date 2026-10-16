using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class HughesBlockExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/HughesBlockExchange.";
    private static readonly Formula Alpha = F.Id("alpha");
    private static readonly Formula U = F.Id("u"), V = F.Id("v"), W = F.Id("w");
    private static readonly Formula Z = F.Id("z"), E = F.Id("E"), M = F.Id("M");
    private static readonly Formula N = F.Id("N"), R = F.Id("r");
    private static readonly Formula Empty = Seq(OpenBracket, CloseBracket);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum run obstruction for a maximal separating block exchange of actual source masks.",
        H("Actual Masks and the Block Exchange Minimum"),
        Blocks(
            Paragraph(Text("Let the alphabet be arbitrary. A word is a finite list. The two "
                + "ordered source words u and v are nonempty; Side.first denotes u and Side.second "
                + "denotes v. A mask records one source at each position, including positions whose "
                + "letters coincide. The ordered projection selects the letters at positions bearing "
                + "one source label. Equal lengths are essential: no position may disappear in a zip.")),
            Node("projection", "Ordered source projections", ProjectionFormula(),
                "Zip letters with labels and select the letters bearing q, preserving position order. "
                + "Optional heads and last elements below are written headOption and lastOption.", false),
            Node("ValidMask", "Actual native source masks", ValidFormula(),
                "The existing binary schedule must consume both sources exactly and evaluate to "
                + "the actual word. An induction on the schedule proves equivalence to equal word "
                + "and schedule lengths with ordered projections exactly u and v. The evaluator "
                + "induction shifts the native occurrence counters when removing a source head.", false),
            Node("rho", "Maximal inserted runs", RhoFormula(),
                "Split the schedule into its maximal homogeneous nonempty blocks, and count the "
                + "blocks headed by the first source. Equivalently, count transitions from the second "
                + "source to the first, placing a virtual second-source label before the schedule.", false),
            Paragraph(Text("A cut E consists of four letter lists X, A, B and Y. The original word "
                + "is XABY and its successor is XBAY. A and B are nonempty; the exterior lists may "
                + "be empty. Transport exchanges the label slices along with these letter blocks. "
                + "The slices have the exact lengths of the corresponding letter blocks. Their "
                + "reassembly and the inverse transport therefore preserve every position.")),
            Node("original", "The original cut word", WordFormula(false),
                "Concatenate X, A, B and Y in their original order.", false),
            Node("successor", "The exchanged word", WordFormula(true),
                "Exchange A and B while leaving both exterior contexts in place.", false),
            Node("back", "The actual back-transport", BackFormula(),
                "Cut N at the successor block lengths and reassemble its four complete slices "
                + "in the original block order. Validity supplies the exact total length.", false),
            Node("Commuting", "Both source projections commute", CommutingFormula(),
                "Use the label slices of the arbitrary successor mask N. For each of the two "
                + "sources, project its letters in A and B and require the two concatenation orders "
                + "to agree. These projections belong to N, rather than to the selected minimum "
                + "mask. Back-transport is valid for the original ordered sources exactly when both "
                + "equations hold, by cancelling the exterior projected words separately.", false),
            Paragraph(Text("Admissibility requires a whole maximal inserted run next to a whole "
                + "separating base block. For a left exchange, A is pure first, B is pure second, "
                + "X does not end first, and Y begins first. For a right exchange, A is pure second, "
                + "B is pure first, X ends first, and Y does not begin first. The nonempty pure blocks "
                + "and all these exterior boundary conditions are retained in Admissible.")),
            Node("Admissible", "Consecutive maximal separating runs", AdmissibleFormula(),
                "The splitBy decomposition places A and B as whole consecutive maximal runs. "
                + "The other neighbouring inserted run is present. The equivalent endpoint "
                + "conditions also allow an empty exterior context.", false),
            Node("IsMinimumMask", "A chosen global minimum mask", MinimumMaskFormula(),
                "The selected mask is actual, has r maximal inserted runs, and no actual mask of "
                + "the same word has fewer runs. The minimum ranges over all masks, including "
                + "different labelings of repeated letters.", false),
            Node("minRuns", "Minimum with an empty-family value", MinRunsFormula(),
                "The least attained natural run count is found by well ordering and then embedded "
                + "in the naturals with infinity. An empty family has value infinity. This definition "
                + "requires neither finiteness nor decidable equality of the alphabet.", false),
            Node("degree", "The all-mask minimum degree", DegreeFormula(),
                "Take the minimum over all actual native masks of the specified word.", false),
            Node("c", "The commuting minimum", RestrictedFormula(false),
                "Take the minimum over valid successor masks satisfying both commutations.", false),
            Node("b", "The noncommuting minimum", RestrictedFormula(true),
                "Take the minimum over valid successor masks failing at least one commutation. "
                + "If there is no such mask, this value is infinity.", false),
            Node("mask_projections", "Native schedule and projection equivalence", MaskProjectionsFormula(),
                "Equal total lengths and both ordered source projections characterize the "
                + "original schedule validity and evaluation. This is the original evaluator induction.", true),
            Node("step", "A single inserted-run start", StepFormula(),
                "A transition contributes one precisely from second to first, and zero otherwise.", false),
            Node("starts", "Recursive inserted-run starts", StartsFormula(),
                "Read every label with the previous label as state. The empty suffix contributes zero.", false),
            Node("lastSide", "The final label with an empty fallback", LastSideFormula(),
                "Return the last actual label, using p only for the empty list.", false),
            Node("starts_append", "Run starts across concatenation", StartsAppendFormula(),
                "The suffix starts from the actual final prefix label, or from p for an empty prefix.", true),
            Node("rho_starts", "Maximal runs and transition starts", RhoStartsFormula(),
                "A virtual initial second label makes the recursive transition count equal to rho.", true),
            Node("projection_append", "Ordered projections across a fitting cut", ProjectionAppendFormula(),
                "Matching prefix word and mask lengths allow both zipped projections to split at the cut.", true),
            Node("projection_pure", "Projection of a pure label block", ProjectionPureFormula(),
                "A complete block is retained for its own label and erased for the other label.", true),
            Node("starts_pure", "Starts of a nonempty pure block", StartsPureFormula(),
                "Only the first transition can contribute in a positive length pure block.", true),
            Node("intended_successor", "The transported admissible successor mask", IntendedFormula(),
                "The actual pure blocks preserve both projections under transport. Maximality "
                + "and the exterior inserted run make exactly one inserted run disappear.", true),
            Node("le_minRuns", "Universal lower bounds for the minimum", LeMinimumFormula(),
                "A lower bound holds for the minimum exactly when it holds for every member, "
                + "including the empty-family infinity case.", true),
            Node("minRuns_le", "Every actual member bounds the minimum", MinimumUpperFormula(),
                "An actual mask in the family supplies an upper bound by its native run count.", true),
            Node("result", "The complete exchange minimum criterion", ResultFormula(),
                "Transport any successor labeling back across the two nonempty exchanged blocks. "
                + "Only boundary transitions change. Comparing the two transition sums shows that "
                + "the inserted-run count changes by at most one, without a purity assumption on "
                + "this arbitrary labeling. For a commuting valid successor mask, back-transport "
                + "is an original mask. Minimality at r therefore forces at least r minus one "
                + "successor runs. The chosen admissible exchange supplies the matching mask: "
                + "its two pure blocks preserve both ordered projections and exactly two adjacent "
                + "inserted runs merge. Thus the commuting minimum equals r minus one. Partition "
                + "all valid successor masks by the two commutation equations to obtain the minimum "
                + "identity and its exactness criterion. The statement includes r equal to two, "
                + "coincident letters, empty exterior contexts, and the infinite noncommuting minimum. "
                + "It concerns insertion-run minima and does not assert an iteration-depth theorem "
                + "or a characterization of a physical channel.", true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool theorem) => Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula ProjectionFormula()
    {
        Formula q = F.Id("q"), p = F.Id("p");
        Formula selector = Lambda("p", Call("ite", Equal(Call("snd", p), q),
            Call("some", Call("fst", p)), Call("none")));
        return Disp(All("alpha", Type(), All("q", F.Id("Side"), All("w", Words(),
            All("M", Masks(), Equal(Call("projection", q, W, M),
                Call("filterMap", selector, Call("zip", W, M))))))));
    }

    private static Formula BackFormula() => Disp(All("alpha", Type(),
        All("E", Call("BlockCut", Alpha), All("N", Masks(), Equal(Call("back", E, N),
            Concat(Call("take", Length(Field("X")), N), ASlice(), BSlice(),
                Call("drop", Add(Add(Length(Field("X")), Length(Field("B"))),
                    Length(Field("A"))), N)))))));

    private static Formula AdmissibleFormula()
    {
        Formula p = F.Id("P"), q = F.Id("Q"), r = F.Id("R"), s = F.Id("S");
        Formula split(Formula x) => Call("splitBy", Lambda("x", Lambda("y",
            Equal(F.Id("x"), F.Id("y")))), x);
        Formula rep(string field, string side) => Call("replicate", Length(Field(field)), F.Id(side));
        Formula pureLeft = And(Equal(q, rep("A", "first")),
            And(Equal(r, rep("B", "second")), Equal(Call("headOption", s), Call("some", F.Id("first")))));
        Formula pureRight = And(Equal(q, rep("A", "second")),
            And(Equal(r, rep("B", "first")), Equal(Call("lastOption", p), Call("some", F.Id("first")))));
        Formula fitted = And(Equal(Length(p), Length(Field("X"))),
            And(Equal(Length(q), Length(Field("A"))),
                And(Equal(Length(r), Length(Field("B"))), Equal(Length(s), Length(Field("Y"))))));
        Formula splitRuns = Equal(split(M), Concat(split(p), Seq(OpenBracket, q, Comma, r, CloseBracket), split(s)));
        Formula body = And(fitted, And(Equal(M, Concat(p, q, r, s)),
            And(splitRuns, new Formula.Logic(pureLeft, FormulaLogicOperator.Or, pureRight))));
        foreach (string name in new[] { "S", "R", "Q", "P" })
            body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Masks(), body);
        return Disp(All("alpha", Type(), All("E", Call("BlockCut", Alpha), All("M", Masks(),
            Iff(Call("Admissible", E, M), And(Nonempty(Field("A")), And(Nonempty(Field("B")), body)))))));
    }

    private static Formula ValidFormula() => WordMaskBind(Iff(Call("ValidMask", U, V, W, M),
        And(Call("ValidTwoSchedule", U, V, M),
            Equal(Call("evaluateTwo", U, V, M), Call("some", W)))));

    private static Formula MaskProjectionsFormula() => WordMaskBind(Iff(Call("ValidMask", U, V, W, M),
        And(Equal(Length(M), Length(W)), And(Equal(Call("projection", F.Id("first"), W, M), U),
            Equal(Call("projection", F.Id("second"), W, M), V)))));

    private static Formula StepFormula() => Disp(All("p", F.Id("Side"), All("q", F.Id("Side"),
        Equal(Call("step", F.Id("p"), F.Id("q")), Call("ite",
            And(Equal(F.Id("p"), F.Id("second")), Equal(F.Id("q"), F.Id("first"))), D(1), D(0))))));

    private static Formula StartsFormula() => Disp(All("p", F.Id("Side"), And(
        Equal(Call("starts", F.Id("p"), Empty), D(0)),
        All("q", F.Id("Side"), All("s", Masks(), Equal(
            Call("starts", F.Id("p"), Call("cons", F.Id("q"), F.Id("s"))),
            Add(Call("step", F.Id("p"), F.Id("q")), Call("starts", F.Id("q"), F.Id("s")))))))));

    private static Formula LastSideFormula() => Disp(All("p", F.Id("Side"), All("s", Masks(),
        Equal(Call("lastSide", F.Id("p"), F.Id("s")),
            Call("getD", Call("lastOption", F.Id("s")), F.Id("p"))))));

    private static Formula StartsAppendFormula() => Disp(All("p", F.Id("Side"), All("s", Masks(),
        All("t", Masks(), Equal(Call("starts", F.Id("p"), Concat(F.Id("s"), F.Id("t"))),
            Add(Call("starts", F.Id("p"), F.Id("s")),
                Call("starts", Call("lastSide", F.Id("p"), F.Id("s")), F.Id("t"))))))));

    private static Formula RhoStartsFormula() => Disp(All("M", Masks(),
        Equal(Call("rho", M), Call("starts", F.Id("second"), M))));

    private static Formula ProjectionAppendFormula() => Disp(All("alpha", Type(), All("q", F.Id("Side"),
        All("a", Words(), All("b", Words(), All("s", Masks(), All("t", Masks(), Implies(
            Equal(Length(F.Id("a")), Length(F.Id("s"))),
            Equal(Call("projection", F.Id("q"), Concat(F.Id("a"), F.Id("b")), Concat(F.Id("s"), F.Id("t"))),
                Concat(Call("projection", F.Id("q"), F.Id("a"), F.Id("s")),
                    Call("projection", F.Id("q"), F.Id("b"), F.Id("t"))))))))))));

    private static Formula ProjectionPureFormula() => Disp(All("alpha", Type(), All("q", F.Id("Side"),
        All("t", F.Id("Side"), All("a", Words(), Equal(
            Call("projection", F.Id("q"), F.Id("a"), Call("replicate", Length(F.Id("a")), F.Id("t"))),
            Call("ite", Equal(F.Id("t"), F.Id("q")), F.Id("a"), Empty)))))));

    private static Formula StartsPureFormula() => Disp(All("p", F.Id("Side"), All("q", F.Id("Side"),
        All("n", Naturals(), Implies(Less(D(0), F.Id("n")),
            Equal(Call("starts", F.Id("p"), Call("replicate", F.Id("n"), F.Id("q"))),
                Call("step", F.Id("p"), F.Id("q"))))))));

    private static Formula IntendedFormula() => Disp(All("alpha", Type(), All("u", Words(), All("v", Words(),
        All("E", Call("BlockCut", Alpha), All("M", Masks(), Implies(
            And(Call("ValidMask", U, V, Call("original", E), M), Call("Admissible", E, M)),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("N"), Masks(),
                And(Call("ValidMask", U, V, Call("successor", E), N), And(Call("Commuting", E, N),
                    Equal(Add(Call("rho", N), D(1)), Call("rho", M))))))))))));

    private static Formula PredicateDomain() => Seq(Masks(), Sp, To, Sp, Call("Prop"));
    private static Formula LeMinimumFormula() => Disp(All("P", PredicateDomain(),
        All("k", Call("WithTop", Naturals()), Iff(AtMost(F.Id("k"), Call("minRuns", F.Id("P"))),
            All("N", Masks(), Implies(Call("P", N), AtMost(F.Id("k"), Call("rho", N))))))));

    private static Formula MinimumUpperFormula() => Disp(All("P", PredicateDomain(),
        All("N", Masks(), Implies(Call("P", N), AtMost(Call("minRuns", F.Id("P")), Call("rho", N))))));

    private static Formula RhoFormula() => Disp(All("M", Masks(),
        Equal(Call("rho", M), Call("countP", Lambda("block",
            Equal(Call("headOption", F.Id("block")), Call("some", F.Id("first")))),
            Call("splitBy", Lambda("x", Lambda("y", Equal(F.Id("x"), F.Id("y")))), M)))));

    private static Formula WordFormula(bool exchanged) => Disp(All("alpha", Type(),
        All("E", Call("BlockCut", Alpha), Equal(Call(exchanged ? "successor" : "original", E),
            Concat(Field("X"), Field(exchanged ? "B" : "A"),
                Field(exchanged ? "A" : "B"), Field("Y"))))));

    private static Formula CommutingFormula() => Disp(All("alpha", Type(),
        All("E", Call("BlockCut", Alpha), All("N", Masks(),
            Iff(Call("Commuting", E, N), And(Commute("first"), Commute("second")))))));

    private static Formula Commute(string q)
    {
        Formula a = Call("projection", F.Id(q), Field("A"), ASlice());
        Formula b = Call("projection", F.Id(q), Field("B"), BSlice());
        return Equal(Concat(a, b), Concat(b, a));
    }

    private static Formula ASlice() => Call("take", Length(Field("A")),
        Call("drop", Add(Length(Field("X")), Length(Field("B"))), N));
    private static Formula BSlice() => Call("take", Length(Field("B")),
        Call("drop", Length(Field("X")), N));

    private static Formula MinimumMaskFormula() => WordMaskBind(All("r", Naturals(),
        Iff(Call("IsMinimumMask", U, V, W, M, R),
            And(Call("ValidMask", U, V, W, M), And(Equal(Call("rho", M), R),
                All("N", Masks(), Implies(Call("ValidMask", U, V, W, N),
                    AtMost(R, Call("rho", N)))))))));

    private static Formula MinRunsFormula()
    {
        Formula p = F.Id("P");
        Formula domain = Seq(Masks(), Sp, To, Sp, Call("Prop"));
        Formula values = new Formula.SetBuilder(Call("rho", M), M, p);
        return Disp(All("P", domain, Equal(Call("minRuns", p),
            Call("min", Seq(values, Sp, Cup, Sp, new Formula.SetLiteral([Infty]))))));
    }

    private static Formula DegreeFormula() => Disp(All("alpha", Type(), All("u", Words(),
        All("v", Words(), All("w", Words(), Equal(Call("degree", U, V, W),
            Call("minRuns", Lambda("M", Call("ValidMask", U, V, W, M)))))))));

    private static Formula RestrictedFormula(bool negative) => Disp(All("alpha", Type(),
        All("E", Call("BlockCut", Alpha), All("u", Words(), All("v", Words(),
            Equal(Call(negative ? "b" : "c", E, U, V), Call("minRuns", Lambda("N",
                And(Call("ValidMask", U, V, Call("successor", E), N),
                    negative ? Seq(Neg, Sp, Call("Commuting", E, N)) :
                        Call("Commuting", E, N))))))))));

    private static Formula ResultFormula()
    {
        Formula threshold = Subtract(R, D(1));
        Formula obstruction = Call("b", E, U, V), degree = Call("degree", U, V, Z);
        Formula conclusion = And(Equal(Call("c", E, U, V), threshold),
            And(Equal(degree, Call("min", threshold, obstruction)),
                Iff(Equal(degree, threshold), AtMost(threshold, obstruction))));
        Formula assumptions = And(Nonempty(U), And(Nonempty(V),
            And(Equal(W, Call("original", E)), And(Equal(Z, Call("successor", E)),
                And(Call("IsMinimumMask", U, V, W, M, R),
                    And(Less(D(1), R), Call("Admissible", E, M)))))));
        return Disp(All("alpha", Type(), All("u", Words(), All("v", Words(),
            All("w", Words(), All("z", Words(), All("E", Call("BlockCut", Alpha),
                All("M", Masks(), All("r", Naturals(), Implies(assumptions, conclusion))))))))));
    }

    private static Formula WordMaskBind(Formula body) => Disp(All("alpha", Type(),
        All("u", Words(), All("v", Words(), All("w", Words(), All("M", Masks(), body))))));
    private static Formula Lambda(string name, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Dot, Sp, body);
    private static Formula Field(string name) => Call(name, E);
    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Words() => Call("List", Alpha);
    private static Formula Masks() => Call("List", F.Id("Side"));
    private static Formula Length(Formula value) => Call("length", value);
    private static Formula Nonempty(Formula value) => Seq(value, Sp, Neq, Sp, Empty);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Concat(params Formula[] parts) => Call("concat", parts);
}
