using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CyclicStableMarriageBlockingBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ishida2026shield");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n >= 1, every complete matching in the cyclic Hollow-Shell profile has at most floor((n - 1)^2 / 4) blocking pairs.",
        H("The cyclic stable-marriage arc-lemma upper bound"),
        Blocks(
            Node("man-rank", "The man's cyclic rank", "rM", RankFormula(woman: false),
                "Equation (1), Section 1.1, p. 2: \"r_M(g, h) = (h − g) mod n + 1, r_W(h, g) = n − (h − g) mod n\". "
                    + "Men and women both have carrier Fin(n), with labels 0 through n - 1. "
                    + "The function val reads a Fin label and ofNat embeds a natural number into the integers. "
                    + "The operator emod is integer Euclidean remainder, exactly the source's mod n; smaller ranks are preferred.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("woman-rank", "The woman's cyclic rank", "rW", RankFormula(woman: true),
                "Equation (1), Section 1.1, p. 2: \"r_M(g, h) = (h − g) mod n + 1, r_W(h, g) = n − (h − g) mod n\". "
                    + "The argument order of rW is woman h, then man g. Both label casts and the integer remainder are displayed explicitly.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blocking-pair", "A blocking pair", "blocks", BlocksFormula(),
                "Section 1.1, p. 1: \"A complete matching µ (a bijection from men to women) has a blocking pair (m_i, w_j) if m_i prefers w_j to µ(m_i) and w_j prefers m_i to µ^{−1}(w_j)\". "
                    + "The letter p denotes the Lean matching μ, represented by Equiv.Perm(Fin(n)); g is a man and h a woman. "
                    + "The displayed function symm(p) is the inverse bijection. Both comparisons are strict, so a matched pair never blocks.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blocking-count", "The blocking-pair count", "B", CountFormula(),
                "Section 1.1, p. 1: \"write B_S(µ) for their number in instance S and β(S) = max_µ B_S(µ)\". "
                    + "Here S is the cyclic profile. The displayed finite comprehension is precisely Finset.univ.filter on Fin(n) × Fin(n), "
                    + "and card is its natural-number cardinality. The functions fst and snd read the man and woman of the ordered pair x. "
                    + "Each ordered man-woman pair is counted once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arc-lemma-claim", "The open arc-lemma upper-bound statement", "claim", ClaimFormula(),
                "Section 7.1, p. 8: \"This statement does not assert that µ∗ is maximum-blocking; that is exactly the open arc-lemma upper-bound problem.\" "
                    + "Conclusion, p. 10: \"It does not claim the exact Shield-Core equality for general n, a universal Hall-feasible biclique theorem, "
                    + "or the general upper bound β(C_n) ≤ ⌊(n − 1)²/4⌋.\" "
                    + "Because β is the maximum over all complete matchings, this upper bound says that every permutation p has the displayed bound. "
                    + "The size n ranges over natural numbers with 1 ≤ n. The subtraction n - 1 is natural subtraction; "
                    + "NatDiv(a, 4) is natural-number division, namely floor(a/4), rather than a rational fraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arc-lemma-result", "The cyclic upper bound", "result", Disp(F.Id("claim")),
                "Split matched edges into U = {i : i ≤ p(i)} and W = {i : p(i) < i}, of sizes k and q. "
                    + "The cyclic rank comparisons divide blocking pairs into inversions within U, inversions within W, and mixed pairs. "
                    + "Across every cut t, the number of edges starting below t and ending at or above t equals the number going the other way, "
                    + "since permutation reindexing preserves the total number of endpoints below t. Applying this balance at p(j) + 1 bounds the U inversions by mixed nesting pairs; "
                    + "applying it at w bounds the W inversions plus q by another disjoint class of mixed pairs. "
                    + "These two classes and the mixed blocking pairs partition W × U, giving B(p) + q ≤ qk. "
                    + "Since k + q = n and (k - q - 1)^2 ≥ 0, we get 4 B(p) ≤ (n - 1)^2 and therefore claim. "
                    + "The conclusion concerns the cyclic profile; the minimum over all preference profiles is a separate question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ishida-2026-cyclic-stable-marriage-blocking-upper-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("cyclic-shield-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Permutations(Formula n) => Call("EquivPerm", Call("Fin", n));

    private static Formula RankFormula(bool woman)
    {
        Formula n = F.Id("n"), g = F.Id("g"), h = F.Id("h");
        Formula offset = Call("emod",
            Subtract(Call("ofNat", Call("val", h)), Call("ofNat", Call("val", g))),
            Call("ofNat", n));
        Formula equality = woman
            ? Equal(Call("rW", h, g), Subtract(Call("ofNat", n), offset))
            : Equal(Call("rM", g, h), Add(offset, D(1)));
        Formula body = woman
            ? All("h", Call("Fin", n), All("g", Call("Fin", n), equality))
            : All("g", Call("Fin", n), All("h", Call("Fin", n), equality));
        return Disp(All("n", Naturals(), body));
    }

    private static Formula BlocksFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), g = F.Id("g"), h = F.Id("h");
        Formula body = Iff(Call("blocks", p, g, h), And(
            Less(Call("rM", g, h), Call("rM", g, Apply(p, g))),
            Less(Call("rW", h, g), Call("rW", h, Apply(Call("symm", p), h)))));
        return Disp(All("n", Naturals(), All("p", Permutations(n),
            All("g", Call("Fin", n), All("h", Call("Fin", n), body)))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), x = F.Id("x");
        Formula pairs = Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", n));
        Formula finiteComprehension = Seq(OpenBrace, x, Colon, Sp, pairs, Sp, Mid, Sp,
            Call("blocks", p, Call("fst", x), Call("snd", x)), CloseBrace);
        return Disp(All("n", Naturals(), All("p", Permutations(n),
            Equal(Call("B", p), Call("card", finiteComprehension)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        Formula bound = Call("NatDiv", new Formula.Power(
            Parenthesized(Subtract(n, D(1))), D(2)), D(4));
        Formula body = All("n", Naturals(), Implies(LessEqual(D(1), n),
            All("p", Permutations(n), LessEqual(Call("B", p), bound))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
