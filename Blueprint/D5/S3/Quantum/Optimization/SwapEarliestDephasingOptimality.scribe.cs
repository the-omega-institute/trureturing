using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class SwapEarliestDephasingOptimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/kaminshchukinschmidtvanloock2023repeaters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complete earliest-pair swapping history minimizes the accumulated dephasing for any finite list of natural ready times.",
        H("Earliest-pair swapping minimizes dephasing"),
        Blocks(
            Node("merge", "Merging adjacent segments", MergeFormula(),
                "At a valid index i, replace the adjacent ready times by their maximum, retaining the prefix and suffix in their original order. "
                    + "This is the shortened list in the source's recurrences (skr.tex, lines 1039–1040 and 1060–1061). "
                    + "Indices start at zero. The function is defined at every natural index: an absent entry is read as zero, "
                    + "take retains the available prefix, and drop removes the indicated number of entries. "
                    + "List.getD(x,i,0) is optional indexing at i followed by Option.getD with default zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("swapCost", "The dephasing of one swap", SwapCostFormula(),
                "The natural difference between the maximum and minimum of two ready times is their absolute difference. "
                    + "It is the dephasing contribution of one adjacent swap (skr.tex, lines 1049–1054). "
                    + "As in merge, an absent entry is read as zero. Nat.sub is subtraction truncated at zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsGreedyStep", "An earliest adjacent pair", GreedyStepFormula(),
                "A greedy step has a valid adjacent-pair index, and the maximum of its two ready times is no greater "
                    + "than that of any other valid adjacent pair. This is the earliest-pair rule "
                    + "(skr.tex, lines 1033–1044). Equality permits every tie choice.",
                AssessedProvenance.FromLiterature(Source)),
            Node("bellman", "One minimization step", BellmanFormula(),
                "Given a natural-valued continuation v, minimize the swap cost plus v of the merged list over all valid first swaps. "
                    + "The finite minimum is taken over i in Finset.range(length(x) − 1); that set is nonempty in the first branch. "
                    + "Lists of length zero or one have value zero. This extends the source's recurrence "
                    + "(skr.tex, lines 1053–1064) to terminal lists.",
                AssessedProvenance.FromLiterature(Source)),
            Node("dstar", "The optimal dephasing", DstarFormula(),
                "Apply the Bellman operator length(x) times to the constant zero function and evaluate at x. "
                    + "Each valid merge removes one entry, so this many steps includes every complete sequence of swaps. "
                    + "This expresses the source's optimal dephasing recurrence and its two-segment base case "
                    + "(skr.tex, lines 1058–1064), with value zero on empty and singleton lists. "
                    + "Function.iterate counts applications of an operator; Function.const displays the constant zero function.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsGreedyRun", "A complete earliest-pair history", GreedyRunFormula(),
                "The list hs records successive adjacent-pair indices in the changing list. "
                    + "The right fold constructs a predicate on the initial list: each recorded index must be greedy "
                    + "at that stage, and the final list must have length at most one. "
                    + "Thus the history expresses repeated earliest-pair choices from skr.tex, lines 1033–1040, "
                    + "while retaining every tie choice explicitly.",
                AssessedProvenance.FromRepo(Source)),
            Node("runCost", "Accumulated dephasing along a history", RunCostFormula(),
                "The right fold constructs a function of the current list, adding the present swap cost "
                    + "to the remaining cost on the merged list. The empty history contributes zero. "
                    + "This function is defined for every hs; the greedy-run predicate separately requires "
                    + "valid indices and completion. On such histories it sums the contributions in "
                    + "skr.tex, lines 1039–1040. Function.const gives the terminal zero function.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "Optimality for every complete greedy history", ClaimFormula(),
                "For every finite list x of natural ready times and every complete greedy history hs, "
                    + "the accumulated dephasing equals dstar(x). This includes the conjecture in "
                    + "skr.tex, lines 1080–1084, for every length at least two and positive ready times. "
                    + "It also includes zero ready times and the empty and singleton lists; no particular tie choice is required.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Every earliest-pair history attains the minimum"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The three anonymous expressions below give the list maximum (zero on the empty list), "
                            + "the integer-valued potential, and the integer-valued boundary function, respectively. "
                            + "In the prose, denote their values by M(x), φ(x), and B(p,x). "
                            + "Every Int.ofNat explicitly includes a natural number in the integers.")),
                    new DocumentBlock.DisplayFormula(FunctionalDefinitions()),
                    Paragraph(Text(
                        "The auxiliary function B separates the first entry: B(p,a :: x) is "
                            + "Int.ofNat(max(p,a)) − Int.ofNat(a) + B(a,x). "
                            + "A merge beyond the first entry commutes with retaining that entry. "
                            + "Every valid merge shortens the list by one and leaves M unchanged. "
                            + "Expanding the sums also gives φ(x) = B(M(x),x), including the empty list.")),
                    Paragraph(Text(
                        "Next induct on the merge index to compare B before and after any valid merge. "
                            + "For a first pair a,b with a ≤ b, the swap cost plus the new B minus the old B is "
                            + "Int.ofNat(max(p,b)) − Int.ofNat(max(p,a)). "
                            + "For a ≥ b it is Int.ofNat(max(a,c)) − Int.ofNat(max(b,c)) if a following entry c exists, "
                            + "and zero if none exists. Both differences are nonnegative. "
                            + "For a later pair the first-entry expansion reduces the comparison to the shorter suffix.")),
                    Paragraph(Text(
                        "The same induction gives equality when the chosen pair has least maximum among all adjacent pairs of p :: x. "
                            + "If a < b, comparison with the pair p,a forces p ≥ b, making the first difference zero. "
                            + "If a > b and c exists, comparison with b,c forces c ≥ a, making the second difference zero. "
                            + "Equal ready times and an absent following entry give zero directly. "
                            + "In the induction step, comparisons in the suffix are inherited by shifting the competing index by one.")),
                    Paragraph(Text(
                        "Now take p = M(x). The additional leading pair M(x),x₀ has maximum M(x), "
                            + "which bounds the maximum of every valid chosen pair. "
                            + "Consequently a greedy pair in x remains least after this entry is prepended. "
                            + "The identity φ(x) = B(M(x),x) and preservation of M therefore give the two comparisons below.")),
                    new DocumentBlock.DisplayFormula(StepComparisons()),
                    Paragraph(Text(
                        "Whenever the list has more than one entry, the nonempty finite set of adjacent-pair indices "
                            + "has an index minimizing its pair maximum, hence a greedy step exists. "
                            + "On lists of length at most one, direct evaluation gives φ(x) = 0.")),
                    Paragraph(Text(
                        "Induct on n to identify n Bellman iterations with φ for every x of length at most n. "
                            + "At n = 0 the list is empty. At a successor, terminal lists again give zero. "
                            + "For a nonterminal list, each merged list is short enough for the induction hypothesis. "
                            + "Choosing a greedy first pair bounds the Bellman minimum above by φ(x), using the equality comparison. "
                            + "Choosing an index attaining that minimum bounds it below by φ(x), using the comparison for every valid pair. "
                            + "The two bounds agree. Setting n = length(x) identifies Int.ofNat(dstar(x)) with φ(x).")),
                    new DocumentBlock.DisplayFormula(IterationIdentity()),
                    Paragraph(Text(
                        "Finally induct on hs. For the empty greedy history the list is terminal, so its cost and φ are zero. "
                            + "For i :: hs, the greedy-run predicate supplies a greedy first step and a complete greedy remaining history "
                            + "on merge(x,i). Cast the cost sum into the integers, apply the induction hypothesis to that remaining history, "
                            + "and use the greedy-step equality to obtain Int.ofNat(runCost(x,i :: hs)) = φ(x). "
                            + "Combining this identity with Int.ofNat(dstar(x)) = φ(x) and injectivity of Int.ofNat proves the stated natural-number equality. "
                            + "The argument includes all natural ready times and every permitted tie choice."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kamin-shchukin-schmidt-van-loock-2023-swap-earliest-dephasing"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(declaration.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MergeFormula() => OverListIndex(Equal(
        Typed(Local("merge", X("x"), X("i")), Lists()),
        At(Qualified("List", "append"), At(Qualified("List", "take"), X("i"), X("x")),
            At(Qualified("List", "cons"), PairMax(X("x"), X("i")),
                At(Qualified("List", "drop"), Add(X("i"), D(2)), X("x"))))));

    private static Formula SwapCostFormula() => OverListIndex(Equal(
        Typed(Local("swapCost", X("x"), X("i")), Naturals()),
        NatSub(PairMax(X("x"), X("i")), At(Qualified("min"),
            Entry(X("x"), X("i")), Entry(X("x"), Add(X("i"), D(1)))))));

    private static Formula GreedyStepFormula() => OverListIndex(Equivalence(
        Local("IsGreedyStep", X("x"), X("i")),
        And(Valid(X("x"), X("i")), All("j", Naturals(), Imp(Valid(X("x"), X("j")),
            LE(PairMax(X("x"), X("i")), PairMax(X("x"), X("j"))))))));

    private static Formula BellmanFormula() => All("v", Arrow(Lists(), Naturals()), All("x", Lists(),
        Equal(Typed(Local("bellman", X("v"), X("x")), Naturals()),
            At(Qualified("ite"), LT(D(1), Length(X("x"))),
                Minimum("i", NatSub(Length(X("x")), D(1)),
                    Add(Local("swapCost", X("x"), X("i")),
                        At(X("v"), Local("merge", X("x"), X("i"))))), D(0)))));

    private static Formula DstarFormula() => All("x", Lists(), Equal(
        Typed(Local("dstar", X("x")), Naturals()), Iterations(Length(X("x")), X("x"))));

    private static Formula GreedyRunFormula() => All("x", Lists(), All("hs", Lists(), Equivalence(
        Local("IsGreedyRun", X("x"), X("hs")),
        At(Qualified("List", "foldr"),
            LambdaOf("i", Naturals(), LambdaOf("r", Arrow(Lists(), Qualified("Prop")),
                LambdaOf("y", Lists(), And(Local("IsGreedyStep", X("y"), X("i")),
                    At(X("r"), Local("merge", X("y"), X("i"))))))),
            LambdaOf("y", Lists(), LE(Length(X("y")), D(1))), X("hs"), X("x")))));

    private static Formula RunCostFormula() => All("x", Lists(), All("hs", Lists(), Equal(
        Typed(Local("runCost", X("x"), X("hs")), Naturals()),
        At(Qualified("List", "foldr"),
            LambdaOf("i", Naturals(), LambdaOf("r", Arrow(Lists(), Naturals()),
                LambdaOf("y", Lists(), Add(Local("swapCost", X("y"), X("i")),
                    At(X("r"), Local("merge", X("y"), X("i"))))))),
            ZeroFunction(), X("hs"), X("x")))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"), ClaimBody());
    private static Formula ClaimBody() => All("x", Lists(), All("hs", Lists(),
        Imp(Local("IsGreedyRun", X("x"), X("hs")),
            Equal(Local("runCost", X("x"), X("hs")), Local("dstar", X("x"))))));

    private static Formula FunctionalDefinitions() => new Formula.Aligned([
        LambdaOf("x", Lists(), Maximum(X("x"))),
        LambdaOf("x", Lists(), PhiAt(X("x"))),
        LambdaOf("p", Naturals(), LambdaOf("x", Lists(), Subtract(
            AsInt(At(Qualified("List", "sum"), At(Qualified("List", "zipWith"), Qualified("max"),
                At(Qualified("List", "cons"), X("p"), X("x")), X("x")))),
            AsInt(At(Qualified("List", "sum"), X("x"))))))
    ]);

    private static Formula StepComparisons() => new Formula.Aligned([
        OverListIndex(Imp(Valid(X("x"), X("i")), LE(PhiAt(X("x")),
            Add(AsInt(Local("swapCost", X("x"), X("i"))), PhiAt(Local("merge", X("x"), X("i"))))))),
        OverListIndex(Imp(Local("IsGreedyStep", X("x"), X("i")), Equal(PhiAt(X("x")),
            Add(AsInt(Local("swapCost", X("x"), X("i"))), PhiAt(Local("merge", X("x"), X("i")))))))
    ]);

    private static Formula IterationIdentity() => All("n", Naturals(), All("x", Lists(),
        Imp(LE(Length(X("x")), X("n")), Equal(AsInt(Iterations(X("n"), X("x"))), PhiAt(X("x"))))));

    private static Formula Iterations(Formula n, Formula x) => At(
        At(Qualified("Function", "iterate"), Local("bellman"), n), ZeroFunction(), x);
    private static Formula ZeroFunction() => At(Qualified("Function", "const"), Lists(), Typed(D(0), Naturals()));
    private static Formula Maximum(Formula x) => At(Qualified("List", "foldr"), Qualified("max"), D(0), x);
    private static Formula PhiAt(Formula x) => Subtract(
        Add(AsInt(Maximum(x)), AsInt(At(Qualified("List", "sum"),
            At(Qualified("List", "zipWith"), Qualified("max"), x, At(Qualified("List", "tail"), x))))),
        AsInt(At(Qualified("List", "sum"), x)));
    private static Formula AsInt(Formula value) => Typed(At(Qualified("Int", "ofNat"), value), Integers());
    private static Formula Entry(Formula x, Formula i) => At(Qualified("List", "getD"), x, i, D(0));
    private static Formula PairMax(Formula x, Formula i) => At(Qualified("max"), Entry(x, i), Entry(x, Add(i, D(1))));
    private static Formula Length(Formula x) => At(Qualified("List", "length"), x);
    private static Formula Valid(Formula x, Formula i) => LT(Add(i, D(1)), Length(x));
    private static Formula NatSub(Formula left, Formula right) => At(Qualified("Nat", "sub"), left, right);
    private static Formula Minimum(string name, Formula end, Formula body) => Seq(
        new Formula.Subscript(Min, Seq(Typed(X(name), Naturals()), Comma, Sp, LT(X(name), end))),
        Sp, Parenthesized(body));
    private static Formula OverListIndex(Formula body) => All("x", Lists(), All("i", Naturals(), body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Lists() => At(Qualified("List"), Naturals());
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name, params Formula[] args)
    {
        Formula function = Qualified("D5", "S3", "Quantum", "Optimization", "SwapEarliestDephasingOptimality", name);
        return args.Length == 0 ? function : At(function, args);
    }
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Left, Open, value, Right, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
