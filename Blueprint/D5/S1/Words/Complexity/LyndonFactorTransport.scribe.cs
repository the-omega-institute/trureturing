using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;
internal sealed class LyndonFactorTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/LyndonFactorTransport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/glensimpsonsmyth2017lyndonfactors");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A suffix-minimum scan computes distinct contiguous Lyndon factor strings.", H("Actual Lyndon factors and elementary transport"), Blocks(
        Paragraph(Text("All scan statements quantify over an arbitrary linearly ordered alphabet A and finite lists. Lexicographic order treats a proper prefix as smaller. The three finite-index definitions are moved from the original refutation, with their namespace and bodies preserved; the original certificate imports this general owner. No new settlement of the original problem is claimed. The supplied Ma–Zhang manuscript gives the suffix-minimum scan argument. The elementary morphism is the classical lambda(a)=a, lambda(b)=ab; its proof uses the existing actual two-factor standard factorization. Richomme's Lyndon-morphism theory is prior literature; no novelty or global priority is asserted.")),
            Node("factor", "Contiguous factors", FactorFormula(),
                "Section 1, p. 1: “A finite word z is said to be a factor of a given finite word w if there exist words u, v such that w = uzv.” Positions start at zero. The displayed list drops i letters and takes l letters from the finite word; occurrences counted below satisfy 1 ≤ l and i + l ≤ n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lyndonOccurrences", "Lyndon-factor occurrences", OccurrencesFormula(),
                "Section 1, p. 2: “A Lyndon word over Σ is a non-empty primitive word that is the lexicographically least word in its conjugacy class, i.e., w ∈ Σ or w < vu for all non-empty words u, v such that w = uv (e.g., see [10]).” IsLyndon is the rotation predicate on lists. The finite set records every valid nonempty occurrence, including repeated occurrences of the same factor and the whole word when it is Lyndon.",
                AssessedProvenance.FromLiterature(Source)),
            Node("distinctLyndon", "Distinct Lyndon factors", DistinctFormula(),
                "Section 5, p. 8: “Let L(w) denote the number of distinct Lyndon factors in a word w.” Taking the image of the occurrence set before its cardinality counts equal factor lists once. Single letters and the whole Lyndon word are included. Section 6, p. 9 gives aaabaaabaab with seven distinct Lyndon factors and aababababab with eight.",
                AssessedProvenance.FromLiterature(Source)),

        N("leastSuffix", "Minimum nonempty suffix", Equal(Call("leastSuffix", F.Id("w")), Call("min", Call("nonemptySuffixes", F.Id("w")))), "For nonempty w this recursively takes the smaller of w and the minimum nonempty suffix of its tail. On the empty input it returns the empty sentinel; that sentinel is never compared in the acceptance test.", DescribeRole.Definition),
        N("suffixScan", "Scan a fixed right endpoint", Equal(Call("suffixScan", F.Id("w")), Call("recordMinima", Call("nonemptySuffixesShortestFirst", F.Id("w")))), "Start with the last letter. Prepend successively longer suffixes; accept exactly when a candidate is strictly less than the minimum already seen. This computes strings by comparisons and never tests IsLyndon.", DescribeRole.Definition),
        N("factorScan", "Identify equal accepted strings", Equal(Call("factorScan", F.Id("w")), Call("toFinset", Call("flatMap", Named("suffixScan"), Call("inits", F.Id("w"))))), "Run suffixScan on every prefix, including the harmless empty prefix, then deduplicate the resulting strings. Thus all right endpoints are covered and repeated occurrences count once.", DescribeRole.Definition),
        N("mem_suffixScan", "Exact suffix scan", Seq(Forall, Sp, F.Id("u"), Sp, F.Id("w"), Comma, F.Id("u"), InMacro, Call("suffixScan", F.Id("w")), Iff, Call("IsLyndon", F.Id("u")), Land, Call("IsSuffix", F.Id("u"), F.Id("w"))), "For every u,w : List A, scan membership is equivalent to u being a Lyndon suffix of w. Induction maintains the minimum of every proper nonempty suffix, and the existing rotation/suffix equivalence supplies precisely the acceptance condition.", DescribeRole.Theorem),
        N("mem_factorScan", "Exact contiguous factor scan", Seq(Forall, Sp, F.Id("u"), Sp, F.Id("w"), Comma, F.Id("u"), InMacro, Call("factorScan", F.Id("w")), Iff, Call("IsLyndon", F.Id("u")), Land, Call("IsInfix", F.Id("u"), F.Id("w"))), "For every u,w : List A, membership is exactly Lyndonness and contiguous occurrence. A substring is a suffix of a prefix. Empty strings are excluded by Lyndonness, while letters and a Lyndon whole word are included.", DescribeRole.Theorem),
        N("factorScan_eq_occurrence_image", "The original occurrence image", WordParameters(Equal(Call("factorScan", Call("List.map", F.Id("w"), Call("List.finRange", F.Id("n")))), Call("Finset.image", Lam(F.Id("p"), Seq(Nats(), Times, Nats()), Call("factor", F.Id("w"), Proj(F.Id("p"), D(1)), Proj(F.Id("p"), D(2)))), Call("lyndonOccurrences", F.Id("w"))))), "For every sigma,n and w : Fin n -> Fin sigma, the scan set equals the image sending each valid pair (i,l) in lyndonOccurrences w to factor w i l. The proof reconstructs a valid slice from an arbitrary contiguous occurrence; its nonemptiness gives l>=1 and its enclosing word gives i+l<=n.", DescribeRole.Theorem),
        N("distinctLyndon_eq_scan", "The original distinct count", WordParameters(Equal(Call("distinctLyndon", F.Id("w")), Call("Finset.card", Call("factorScan", Call("List.map", F.Id("w"), Call("List.finRange", F.Id("n"))))))), "The original distinctLyndon count is exactly the cardinality of the scan set. This is an equality of the actual factor objects, with no count recurrence or occurrence-count replacement.", DescribeRole.Theorem),
        N("mapWord", "Letter-image morphism", Equal(Call("mapWord", F.Id("f"), F.Id("w")), Call("List.flatMap", F.Id("f"), F.Id("w"))), "For f : Fin 2 -> List (Fin 2), concatenate the letter images in their input order.", DescribeRole.Definition),
        N("elementaryLeft", "The elementary left morphism", Equal(Call("elementaryLeft", F.Id("a")), Call("lambda", F.Id("a"))), "The smaller letter 0 maps to [0], and the larger letter 1 maps to [0,1].", DescribeRole.Definition),
        N("elementaryLeft_lyndon_iff", "Actual elementary preservation and reflection", Seq(Forall, Sp, F.Id("w"), Comma, Call("IsLyndon", Call("mapWord", Named("elementaryLeft"), F.Id("w"))), Iff, Call("IsLyndon", F.Id("w"))), "For every binary list w, including letters and the empty list, lambda(w) is Lyndon iff w is Lyndon. Preservation inducts through the actual standard left and right Lyndon factors; reflection uses strict order preservation and actual concatenated images of rotations. This does not assert a factor-set identity on the wider domain.", DescribeRole.Theorem),
        N("elementaryLeft_factor_growth", "An additional factor outside the morphism image", Seq(Forall, Sp, F.Id("w"), Comma, F.D(1), InMacro, Sp, F.Id("w"), Rightarrow, Call("card", Call("factorScan", F.Id("w"))), Plus, F.D(1), Leq, Call("card", Call("factorScan", Call("mapWord", Named("elementaryLeft"), F.Id("w"))))), "For every binary list w containing the letter 1, the lambda image has at least one more distinct Lyndon factor. Every input Lyndon factor maps injectively to an actual output factor, while [1] occurs and is outside the image because every nonempty lambda image starts with 0. This is a proved lower bound, not the still-open exact factor-set identity or exact count increment.", DescribeRole.Theorem),
        Paragraph(Text("Open boundaries: general block factor sets/counts, rho and arbitrary composite transport, original h and its factor-count +8 identity, and exact nested sets remain unproved here. Scan correctness does not certify the retained 220-row data, CF/word correspondence, Fibonacci family, arbitrary-alphabet minima, or the 9082 comparison. Saari's equality/length obligations, GSS's specific Christoffel domain, and the unavailable Glen2018 proof boundary remain unchanged. The theorem-specific unfinished registration disclosure is linked under issue 29680; no declared_validated registration is claimed.")))));
    private static DocumentBlock N(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Node(name, title, Disp(formula), prose, AssessedProvenance.FromRepo(Source), role);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("lyndon-transport-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lam(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Proj(Formula p, Formula digit) => Seq(p, Dot, digit);
    private static Formula WordParameters(Formula body)
    {
        Formula sigma = SigmaLower, n = F.Id("n"), w = F.Id("w");
        return All(sigma, Nats(), All(n, Nats(), All(w, Fn(Fin(n), Fin(sigma)), body)));
    }

    private static Formula FactorFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), i = F.Id("i"), l = F.Id("l");
        return Disp(WordParameters(All(i, Nats(), All(l, Nats(),
            Equal(Call("factor", w, i, l),
                Call("List.take", l, Call("List.drop", i, Call("List.map", w, Call("List.finRange", n)))))))));
    }

    private static Formula OccurrencesFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), p = F.Id("p");
        Formula i = Proj(p, D(1)), l = Proj(p, D(2));
        Formula condition = And(Le(D(1), l), And(Le(new Formula.Binary(i, FormulaBinaryOperator.Add, l), n),
            Call("IsLyndon", Call("factor", w, i, l))));
        Formula pairs = Call("Finset.product", Call("Finset.range", n),
            Call("Finset.range", new Formula.Binary(n, FormulaBinaryOperator.Add, D(1))));
        return Disp(WordParameters(Equal(Call("lyndonOccurrences", w),
            Call("Finset.filter", Lam(p, Seq(Nats(), Sp, Times, Sp, Nats()), condition), pairs))));
    }

    private static Formula DistinctFormula()
    {
        Formula w = F.Id("w"), p = F.Id("p");
        return Disp(WordParameters(Equal(Call("distinctLyndon", w),
            Call("Finset.card", Call("Finset.image",
                Lam(p, Seq(Nats(), Sp, Times, Sp, Nats()), Call("factor", w, Proj(p, D(1)), Proj(p, D(2)))),
                Call("lyndonOccurrences", w))))));
    }

}
