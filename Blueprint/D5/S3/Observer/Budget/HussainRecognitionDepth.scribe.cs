using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class HussainRecognitionDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/HussainRecognitionDepth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/hussain2026decisiontrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact deterministic recognition depth in Hussain's Question 3 stabilizes.",
        H("Eventual constancy of deterministic recognition depth"),
        Blocks(
            Definition("source-tree", "SourceTree", "Source recognition tree", SourceTree(),
                "This inductive tree starts below the source's unique unlabeled root edge. "
                + "A terminal node carries a state label. At a query node the next subtree is "
                + "indexed by a member of the nonempty set of present letters."),
            Definition("complete-path", "CompletePath", "Complete paths", CompletePath(),
                "A complete path ends at a terminal node. Its step constructor prepends the "
                + "current query and the underlying letter of the selected branch."),
            Definition("compatible", "Compatible", "Path compatibility", Compatible(),
                "A query and answer along the path are compatible with the input state when "
                + "the readout returns that answer for that query."),
            Definition("depth-le", "DepthLE", "Complete path depth bound", DepthLE(),
                "The bound covers every complete path, including paths incompatible with all inputs."),
            Definition("recognizes", "Recognizes", "Recognition on a promise", Recognizes(),
                "Every input has a compatible complete path. Every compatible complete path "
                + "has that input as its terminal label."),
            Definition("source-exact-at-depth", "SourceExactAtDepth", "Feasible source depth",
                SourceExactAtDepth(), "For an empty state type every natural depth is feasible. "
                + "Otherwise a source tree must recognize the inputs within the given bound."),
            Definition("promise", "Promise", "Length promise", Promise(),
                "A state is a coordinate array whose associated list is in the language. "
                + "The brace expression denotes a subtype.", fromRepo: true),
            Definition("coordinate-readout", "coordinateReadout", "Coordinate readout",
                CoordinateReadout(), "The projection of the promised word is the underlying array.",
                fromRepo: true),
            Definition("recognition-depth", "recognitionDepth", "Minimum recognition depth",
                RecognitionDepth(), "Lean's Nat.find takes the proof that some depth is feasible "
                + "for this readout. Its value is zero on the empty promise."),
            Definition("subword-closed", "SubwordClosed", "Closure under scattered subwords",
                SubwordClosed(), "List.Sublist allows deletions at arbitrary positions."),
            Definition("hom-exponents", "HomExponents", "Homogeneity exponent set",
                HomExponents(), "Definition 9 includes every natural exponent for which the "
                + "two equal-letter blocks with a distinct letter between them form a word in the language."),
            Definition("het-exponents", "HetExponents", "Heterogeneity exponent set",
                HetExponents(), "Definition 10 includes every natural exponent for which the "
                + "two distinct-letter blocks form a word in the language."),
            Describe.Lean(
                DescribeId.Create("hussain-recognition-depth-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Question 3"),
                StatementSource.FromAuthor(Disp(Equivalent(Operator("claim"), Claim()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The two finite exponent sets define the source's Hom and Het "
                    + "dimensions. An empty exponent set gives dimension zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hussain-recognition-depth-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact minimum depth stabilizes"),
                StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Below the unique unlabeled root edge, a query node has a nonempty "
                        + "set of distinct letter branches, and each leaf is labeled by a promised "
                        + "word. Each promised input has a compatible complete path, and every "
                        + "compatible path returns that input. The depth bound applies to every "
                        + "complete path. The empty promise has minimum depth zero.")),
                    Paragraph(Text("Complete missing branches by terminating them immediately. "
                        + "Two promised inputs with the same transcript then reach the same leaf. "
                        + "In reverse, label a protocol leaf by the unique promised input reaching "
                        + "it, or by an arbitrary promised word on unreachable leaves. These "
                        + "constructions preserve each depth bound. Querying every coordinate "
                        + "supplies a finite bound, so the two minimum depths exist and agree.")),
                    Paragraph(Text("Given upper bounds m and h for the Hom and Het exponents, "
                        + "put c equal to one plus the alphabet size times the larger bound. "
                        + "For a word of length n+1 with n at least 2c+1, the regions strictly "
                        + "before and after the positions c and c+1 each contain at least c "
                        + "letters. Each region contains at least max(m,h)+1 copies of one letter. "
                        + "The Het bound forces those letters to coincide. The Hom bound forces "
                        + "each intervening letter to be that same letter.")),
                    Paragraph(Text("Delete coordinate c+1. The shorter word belongs to the shorter "
                        + "promise, and inserting the retained letter at coordinate c reconstructs "
                        + "the original word. Relabel the queries of a shorter protocol by the "
                        + "surviving coordinates. This preserves the depth bound and all transcripts "
                        + "on the deletion image, which gives the inequality "),
                        Math(In(Le(Call("recognitionDepth", F.Id("L"), Add(F.Id("n"), D(1))),
                            Call("recognitionDepth", F.Id("L"), F.Id("n"))))),
                        Text(" on the tail. A nonincreasing natural-valued sequence is eventually constant."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hussain-2026-recognition-depth-question-3"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, Formula formula, string explanation,
        bool fromRepo = false) =>
        Describe.Lean(DescribeId.Create("hussain-recognition-depth-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            fromRepo ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula SourceTree()
    {
        Formula letters = F.Id("E"), tree = TreeType();
        return Rows(
            For(Seq(tree, Colon, Type(Call("max", F.Id("u"), F.Id("v"), F.Id("w")))),
                TreeBinders()),
            Seq(Operator("terminal"), Colon, Arrow(F.Id("S"), tree)),
            Seq(Operator("query"), Colon,
                Arrow(F.Id("Q"), For(
                    Arrow(QualifiedCall("Set", "Nonempty", letters), Arrow(Arrow(letters, tree), tree)),
                    Typed("E", Call("Set", F.Id("A")))))));
    }

    private static Formula CompletePath()
    {
        Formula state = F.Id("s"), coordinate = F.Id("q"), answer = F.Id("a");
        Formula letters = F.Id("E"), present = F.Id("h"), next = F.Id("f"), tail = F.Id("p");
        Formula query = Call("query", coordinate, letters, present, next);
        Formula edge = Seq(Open, coordinate, Comma, Field(answer, 1), Close);
        Formula step = Arrow(Call("CompletePath", Apply(next, answer), tail, state),
            Call("CompletePath", query, Seq(edge, Sp, Colon, Colon, Sp, tail), state));
        return Rows(
            For(Seq(Operator("CompletePath"), Colon,
                    Arrow(TreeType(), Arrow(PathType(), Arrow(F.Id("S"), Operator("Prop"))))),
                TreeBinders()),
            Seq(Operator("terminal"), Colon,
                For(Call("CompletePath", Call("terminal", state), EmptyList(), state),
                    Typed("s", F.Id("S")))),
            Seq(Operator("step"), Colon,
                For(step, Typed("q", F.Id("Q")), Typed("E", Call("Set", F.Id("A"))),
                    Typed("h", QualifiedCall("Set", "Nonempty", letters)),
                    Typed("f", Arrow(letters, TreeType())),
                    Typed("p", PathType()), Typed("s", F.Id("S")), Typed("a", letters))));
    }

    private static Formula Compatible()
    {
        Formula readout = F.Id("r"), state = F.Id("s"), path = F.Id("p"), edge = F.Id("e");
        Formula agrees = Equal(Apply(readout, Field(edge, 1), state), Field(edge, 2));
        return For(Equivalent(Call("Compatible", readout, state, path),
                For(ImpliesFormula(Member(edge, path), agrees), Typed("e", EdgeType()))),
            [.. TreeBinders(), Typed("r", ReadoutType()), Typed("s", F.Id("S")), Typed("p", PathType())]);
    }

    private static Formula DepthLE()
    {
        Formula tree = F.Id("T"), path = F.Id("p"), label = F.Id("s"), depth = F.Id("d");
        return For(Equivalent(Call("DepthLE", tree, depth),
                For(ImpliesFormula(Call("CompletePath", tree, path, label),
                        Le(QualifiedCall("List", "length", path), depth)),
                    Typed("p", PathType()), Typed("s", F.Id("S")))),
            [.. TreeBinders(), Typed("T", TreeType()), Typed("d", Naturals())]);
    }

    private static Formula Recognizes()
    {
        Formula readout = F.Id("r"), tree = F.Id("T"), state = F.Id("s");
        Formula path = F.Id("p"), label = F.Id("b");
        Formula complete = Call("CompletePath", tree, path, label);
        Formula compatible = Call("Compatible", readout, state, path);
        Formula covers = For(Some(Logical(complete, FormulaLogicOperator.And, compatible),
            Typed("p", PathType()), Typed("b", F.Id("S"))), Typed("s", F.Id("S")));
        Formula sound = For(ImpliesFormula(complete, ImpliesFormula(compatible, Equal(label, state))),
            Typed("s", F.Id("S")), Typed("p", PathType()), Typed("b", F.Id("S")));
        return Rows(
            For(Seq(Call("Recognizes", readout, tree), Sp, Iff),
                [.. TreeBinders(), Typed("r", ReadoutType()), Typed("T", TreeType())]),
            Seq(Open, covers, Close, Sp, Land),
            Seq(Open, sound, Close));
    }

    private static Formula SourceExactAtDepth()
    {
        Formula readout = F.Id("r"), tree = F.Id("T"), depth = F.Id("d");
        Formula feasible = Some(Logical(Call("DepthLE", tree, depth), FormulaLogicOperator.And,
            Call("Recognizes", readout, tree)), Typed("T", TreeType()));
        return Rows(
            For(Seq(Call("SourceExactAtDepth", readout, depth), Sp, Iff),
                [.. TreeBinders(), Typed("r", ReadoutType()), Typed("d", Naturals())]),
            Logical(Call("IsEmpty", F.Id("S")), FormulaLogicOperator.Or, Seq(Open, feasible, Close)));
    }

    private static Formula Promise()
    {
        Formula language = F.Id("L"), length = F.Id("n"), word = F.Id("w");
        Formula state = SetOf("w", Arrow(Call("Fin", length), F.Id("A")),
            Member(QualifiedCall("List", "ofFn", word), language));
        return For(Equal(Call("Promise", language, length), state),
            [.. LanguageBinders(), Typed("n", Naturals())]);
    }

    private static Formula CoordinateReadout()
    {
        Formula language = F.Id("L"), length = F.Id("n"), word = F.Id("w"), coordinate = F.Id("i");
        return For(Equal(Call("coordinateReadout", coordinate, word), Apply(Field(word, 1), coordinate)),
            [.. LanguageBinders(), Typed("n", Naturals()), Typed("i", Call("Fin", length)),
                Typed("w", Call("Promise", language, length))]);
    }

    private static Formula RecognitionDepth()
    {
        Formula alphabet = F.Id("A"), language = F.Id("L"), length = F.Id("n");
        Formula readout = new Formula.Subscript(Operator("coordinateReadout"),
            Seq(alphabet, Comma, language, Comma, length));
        Formula feasible = SetOf("d", Naturals(), Call("SourceExactAtDepth", readout, F.Id("d")));
        return For(Equal(Call("recognitionDepth", language, length), Seq(Min, Sp, feasible)),
            [.. LanguageBinders(finite: true), Typed("n", Naturals())]);
    }

    private static Formula SubwordClosed()
    {
        Formula language = F.Id("L"), smaller = F.Id("u"), larger = F.Id("v");
        Formula closed = For(ImpliesFormula(QualifiedCall("List", "Sublist", smaller, larger),
            ImpliesFormula(Member(larger, language), Member(smaller, language))),
            Typed("u", WordType()), Typed("v", WordType()));
        return For(Equivalent(Call("SubwordClosed", language), closed), LanguageBinders());
    }

    private static Formula HomExponents()
    {
        Formula block = QualifiedCall("List", "replicate", F.Id("e"), F.Id("a"));
        Formula singleton = Seq(OpenBracket, F.Id("b"), CloseBracket);
        Formula prefix = QualifiedCall("List", "append", block, singleton);
        return ExponentSet("HomExponents", QualifiedCall("List", "append", prefix, block));
    }

    private static Formula HetExponents() => ExponentSet("HetExponents", QualifiedCall("List", "append",
        QualifiedCall("List", "replicate", F.Id("e"), F.Id("a")),
        QualifiedCall("List", "replicate", F.Id("e"), F.Id("b"))));

    private static Formula ExponentSet(string name, Formula pattern)
    {
        Formula language = F.Id("L"), alphabet = F.Id("A");
        Formula distinct = new Formula.Relation(F.Id("a"), FormulaRelationOperator.NotEqual, F.Id("b"));
        Formula occurs = Some(Logical(distinct, FormulaLogicOperator.And, Member(pattern, language)),
            Typed("a", alphabet), Typed("b", alphabet));
        return For(Equal(Call(name, language), SetOf("e", Naturals(), occurs)), LanguageBinders());
    }

    private static Formula Claim()
    {
        Formula a = F.Id("A"), l = F.Id("L"), n = F.Id("n"), start = F.Id("N"), d = F.Id("d");
        Formula settles = Logical(Le(D(1), start), FormulaLogicOperator.And,
            Seq(Open, For(ImpliesFormula(Le(start, n), Equal(Call("recognitionDepth", l, n), d)),
                Typed("n", Naturals())), Close));
        return Rows(
            For(Seq(Le(D(2), QualifiedCall("Fintype", "card", a)), Sp, Longrightarrow),
                LanguageBinders(finite: true)),
            Seq(Call("SubwordClosed", l), Sp, Longrightarrow),
            Seq(QualifiedCall("Set", "Finite", Call("HomExponents", l)), Sp, Longrightarrow),
            Seq(QualifiedCall("Set", "Finite", Call("HetExponents", l)), Sp, Longrightarrow),
            Some(settles, Typed("N", Naturals()), Typed("d", Naturals())));
    }

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => Apply(Operator(name), args);
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), args);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Type(Formula level) => new Formula.Subscript(Operator("Type"), level);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Field(Formula value, byte field) => Seq(value, Dot, D(field));
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula Rows(params Formula[] rows) =>
        new Formula.Aligned([.. rows.Select(static row => Seq(Amp, row))]);
    private static Formula Typed(string name, Formula domain) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Close);
    private static Formula For(Formula body, params Formula[] binders) => Quantify(Forall, body, binders);
    private static Formula Some(Formula body, params Formula[] binders) => Quantify(Exists, body, binders);
    private static Formula Quantify(Formula quantifier, Formula body, Formula[] binders) =>
        Seq(quantifier, Sp, Seq(binders), Comma, Quad, Sp, body);
    private static Formula SetOf(string name, Formula domain, Formula predicate) =>
        Seq(Left, OpenBrace, F.Id(name), Colon, Sp, domain,
            Sp, Mid, Sp, predicate, Right, CloseBrace);
    private static Formula Logical(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);
    private static Formula Equivalent(Formula left, Formula right) =>
        Logical(left, FormulaLogicOperator.Iff, right);
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Logical(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula element, Formula collection) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, collection);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TreeType() => Call("SourceTree", F.Id("A"), F.Id("Q"), F.Id("S"));
    private static Formula ReadoutType() => Arrow(F.Id("Q"), Arrow(F.Id("S"), F.Id("A")));
    private static Formula EdgeType() => Seq(F.Id("Q"), Sp, Times, Sp, F.Id("A"));
    private static Formula PathType() => Call("List", EdgeType());
    private static Formula WordType() => Call("List", F.Id("A"));
    private static Formula[] TreeBinders() =>
        [Typed("A", Type(F.Id("u"))), Typed("Q", Type(F.Id("v"))), Typed("S", Type(F.Id("w")))];
    private static Formula[] LanguageBinders(bool finite = false) => finite
        ? [Typed("A", Type(F.Id("u"))), Seq(OpenBracket, Call("Fintype", F.Id("A")), CloseBracket),
            Typed("L", Call("Set", WordType()))]
        : [Typed("A", Type(F.Id("u"))), Typed("L", Call("Set", WordType()))];
}
