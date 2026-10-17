using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class UnaryGapWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/UnaryGapWords.";
    private static readonly Formula A = F.Id("a"), C = F.Id("cs"), Hs = F.Id("h");
    private static readonly Formula E = F.Id("e"), W = F.Id("w"), M = F.Id("M");
    private static readonly Formula Q = F.Id("q");
    private static Formula Words => Call("List", F.Id("alpha"));
    private static Formula Masses => Call("List", Naturals());
    private static Formula Masks => Call("List", F.Id("Side"));
    private static Formula Gap(Formula c, Formula h) => Call("gap", A, c, h);
    private static Formula AddMass(Formula h, Formula e) => Call("zipWith", F.Id("add"), h, e);
    private static Formula Away(Formula c) => All("x", F.Id("alpha"),
        Implies(Member(F.Id("x"), c), NotEqual(F.Id("x"), A)));
    private static Formula Lengths(Formula c, Formula h) =>
        Equal(Call("length", h), Add(Call("length", c), Num(1)));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula BindBase(Formula body) => All("alpha", Type(),
        All("a", F.Id("alpha"), All("cs", Words, All("h", Masses, body))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrence-indexed unary gaps and complete positional source traces.",
        H("Unary Gaps of Actual Words"), Blocks(
            Paragraph(Text("Fix a letter a in an arbitrary alphabet. A gap word alternates "
                + "blocks of a with a list of non-a occurrences. The list preserves repeated "
                + "letters as separate occurrences. Its gap vector has one more entry than "
                + "its occurrence list; entries may be zero.")),
            Node("gap", "Gap concatenation", BindBase(Seq(Call("gap", A, C, Hs), Sp, Colon, Sp, Words)),
                "For an empty occurrence list, take the first gap's copies of a. For c followed "
                + "by cs, concatenate the first a block, c, and the remaining gap word. "
                + "All uses of a gap presentation supply exactly one more mass than occurrences.", false),
            Node("spine", "Non-a occurrences", All("alpha", Type(), All("a", F.Id("alpha"),
                All("w", Words, Equal(Call("spine", A, W),
                    Call("filter", F.Id("notEqualToA"), W))))),
                "Filter the actual word by inequality to a without removing multiplicities.", false),
            Node("sizes", "Canonical gap lengths", All("alpha", Type(), All("a", F.Id("alpha"),
                All("w", Words, Seq(Call("sizes", A, W), Sp, Colon, Sp, Masses)))),
                "Scan from the right. An a increments the first gap; a non-a occurrence starts "
                + "a new zero gap. The empty word has the single gap zero.", false),
            Node("gap_injective", "Uniqueness of indexed gap words", BindBase(
                All("ds", Words, All("k", Masses, Implies(And(Away(C),
                    And(Away(F.Id("ds")), And(Lengths(C, Hs), Lengths(F.Id("ds"), F.Id("k"))))),
                    Implies(Equal(Gap(C, Hs), Gap(F.Id("ds"), F.Id("k"))),
                        And(Equal(C, F.Id("ds")), Equal(Hs, F.Id("k")))))))),
                "Recovering the spine and lengths from each actual concatenation proves both "
                + "equalities, including repeated separators and zero gaps.", true),
            Node("gap_exists", "Every word has a canonical presentation", All("alpha", Type(),
                All("a", F.Id("alpha"), All("w", Words,
                    Ex("cs", Words, Ex("h", Masses, And(Away(C),
                        And(Lengths(C, Hs), Equal(W, Gap(C, Hs))))))))),
                "The canonical spine and gap lengths reconstruct the original word.", true),
            Node("Trace", "Complete gap labels", BindBase(All("q", F.Id("Side"),
                All("e", Masses, All("w", Words, All("M", Masks,
                    Seq(Call("Trace", A, Q, C, Hs, E, W, M), Sp, Colon, Sp, Call("Prop"))))))),
                "Every a gap retains its whole label list b. Its q count contributes to h, "
                + "and its opposite-source count contributes to e. Every non-a occurrence "
                + "has label q. This is an inductive decomposition of actual letters and labels.", false),
            Node("grouped", "Grouped labels in each gap", All("alpha", Type(),
                All("q", F.Id("Side"), All("cs", Words, All("h", Masses,
                    All("e", Masses, Seq(Call("grouped", Q, C, Hs, E), Sp, Colon, Sp, Masks)))))),
                "With a unary inserted source, place its gap mass together after the base "
                + "copies. With a unary base source, place base copies before the inserted "
                + "copies in each nonterminal gap, and after them in the terminal gap.", false),
            Node("native_gap_iff", "Unique extra masses and actual masks", NativeFormula(),
                "For each native projection pair, non-a letters are forced to q. Splitting "
                + "at those occurrences gives every label gap and both projected words. "
                + "Conversely, grouped gap labels realize every permitted mass vector. "
                + "Canonical word recovery makes the extra vector unique. No alphabet order, "
                + "decidable equality premise or distinctness between separators is assumed.", true),
            Node("profile_gap", "Canonical recovery of a presented gap word", BindBase(Implies(
                And(Away(C), Lengths(C, Hs)), And(Equal(Call("spine", A, Gap(C, Hs)), C),
                    Equal(Call("sizes", A, Gap(C, Hs)), Hs)))),
                "Filtering recovers exactly the occurrence list, and the canonical gap scan "
                + "recovers exactly the supplied lengths.", true),
            Node("trace_projections", "Both projections of a positional trace", TraceBind(Implies(
                Call("Trace", A, Q, C, Hs, E, W, M),
                And(Equal(Call("length", M), Call("length", W)), And(Lengths(C, Hs),
                    And(Equal(Call("length", E), Call("length", Hs)), And(Away(C),
                        And(Equal(Call("projection", Q, W, M), Gap(C, Hs)),
                            And(Equal(Call("projection", Call("opposite", Q), W, M),
                                Call("replicate", Call("sum", E), A)),
                                Equal(W, Gap(C, AddMass(Hs, E))))))))))),
                "The trace gives matching word and mask lengths, both ordered source "
                + "projections, all vector lengths and the actual enlarged gap word.", true),
            Node("trace_exists", "Extracting the full trace", All("alpha", Type(),
                All("a", F.Id("alpha"), All("q", F.Id("Side"), All("w", Words, All("M", Masks,
                    Implies(And(Equal(Call("length", M), Call("length", W)),
                        All("x", F.Id("alpha"), Implies(Member(F.Id("x"),
                            Call("projection", Call("opposite", Q), W, M)), Equal(F.Id("x"), A)))),
                        Ex("cs", Words, Ex("h", Masses, Ex("e", Masses,
                            Call("Trace", A, Q, C, Hs, E, W, M)))))))))),
                "At each non-a occurrence the opposite projection excludes its label. "
                + "Splitting there retains every intervening label and all zero gaps.", true),
            Node("trace_construct", "Realizing every extra vector", BindBase(All("q", F.Id("Side"),
                All("e", Masses, Implies(And(Away(C), And(Lengths(C, Hs),
                    Equal(Call("length", E), Call("length", Hs)))),
                    Call("Trace", A, Q, C, Hs, E, Gap(C, AddMass(Hs, E)),
                        Call("grouped", Q, C, Hs, E)))))),
                "The grouped mask realizes each permitted vector on an actual gap word, "
                + "including the no-separator case and both exterior masses.", true),
            Node("trace_of_projections", "Recovering prescribed gap masses", TraceBind(Implies(
                And(Away(C), And(Lengths(C, Hs), And(Equal(Call("length", E), Call("length", Hs)),
                    And(Equal(W, Gap(C, AddMass(Hs, E))),
                        And(Equal(Call("length", M), Call("length", W)),
                            And(Equal(Call("projection", Q, W, M), Gap(C, Hs)),
                                All("x", F.Id("alpha"), Implies(Member(F.Id("x"),
                                    Call("projection", Call("opposite", Q), W, M)), Equal(F.Id("x"), A))))))))),
                Call("Trace", A, Q, C, Hs, E, W, M))),
                "Actual word uniqueness identifies the extracted original and extra gaps "
                + "with their prescribed vectors, without identifying repeated separators.", true),
            Node("gap_insert", "Transport at an actual word cut", InsertFormula(),
                "Let i count the non-a occurrences in X. Then i is a valid gap index. "
                + "Inserting k copies of a at X|Y adds k only to e[i], preserves vector "
                + "length, increases its sum by k, and gives exactly the concatenated word "
                + "X followed by a^k followed by Y. This is an identity on actual words.", true))));

    private static Formula InsertFormula()
    {
        Formula x = F.Id("X"), y = F.Id("Y"), k = F.Id("k");
        Formula i = Call("length", Call("spine", A, x));
        Formula changed = Call("modify", E, i, Call("add", k));
        Formula assumptions = And(Away(C), And(Lengths(C, Hs),
            And(Equal(Call("length", E), Call("length", Hs)),
                Equal(Call("append", x, y), Gap(C, AddMass(Hs, E))))));
        Formula conclusions = And(new Formula.Relation(i, FormulaRelationOperator.LessThan, Call("length", E)),
            And(Equal(Call("length", changed), Call("length", Hs)),
                And(Equal(Call("sum", changed), Add(Call("sum", E), k)),
                    Equal(Call("append", Call("append", x, Call("replicate", k, A)), y),
                        Gap(C, AddMass(Hs, changed))))));
        return BindBase(All("e", Masses, All("X", Words, All("Y", Words,
            All("k", Naturals(), Implies(assumptions, conclusions))))));
    }

    private static Formula TraceBind(Formula body) => BindBase(All("q", F.Id("Side"),
        All("e", Masses, All("w", Words, All("M", Masks, body)))));

    private static Formula NativeFormula()
    {
        Formula opposite = Call("opposite", Q);
        Formula left = Ex("M", Masks, And(Equal(Call("length", M), Call("length", W)),
            And(Equal(Call("projection", Q, W, M), Gap(C, Hs)),
                Equal(Call("projection", opposite, W, M), Call("replicate", F.Id("m"), A)))));
        Formula valid(Formula e) => And(Equal(Call("length", e), Call("length", Hs)),
            And(Equal(Call("sum", e), F.Id("m")), Equal(W, Gap(C, AddMass(Hs, e)))));
        Formula unique = Ex("e", Masses, And(valid(E), All("f", Masses,
            Implies(valid(F.Id("f")), Equal(F.Id("f"), E)))));
        return Disp(BindBase(All("q", F.Id("Side"), All("m", Naturals(), All("w", Words,
            Implies(And(Away(C), Lengths(C, Hs)), Iff(left, unique)))))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool theorem) => Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Type() => Call("Type");
    private static Formula Naturals() => Call("Nat");
    private static Formula Member(Formula x, Formula xs) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, xs);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

}
