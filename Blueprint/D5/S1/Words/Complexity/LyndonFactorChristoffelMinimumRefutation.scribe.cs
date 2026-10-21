using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class LyndonFactorChristoffelMinimumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/glensimpsonsmyth2017lyndonfactors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary Lyndon word of length 506 has sixteen distinct Lyndon factors, fewer than every Christoffel word of that length.",
        H("Christoffel words need not attain the Lyndon-factor minimum"),
        Blocks(
            Node("factor", "Contiguous factors", FactorFormula(),
                "Section 1, p. 1: “A finite word z is said to be a factor of a given finite word w if there exist words u, v such that w = uzv.” Positions start at zero. The displayed list drops i letters and takes l letters from the finite word; occurrences counted below satisfy 1 ≤ l and i + l ≤ n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lyndonOccurrences", "Lyndon-factor occurrences", OccurrencesFormula(),
                "Section 1, p. 2: “A Lyndon word over Σ is a non-empty primitive word that is the lexicographically least word in its conjugacy class, i.e., w ∈ Σ or w < vu for all non-empty words u, v such that w = uv (e.g., see [10]).” IsLyndon is the rotation predicate on lists. The finite set records every valid nonempty occurrence, including repeated occurrences of the same factor and the whole word when it is Lyndon.",
                AssessedProvenance.FromLiterature(Source)),
            Node("distinctLyndon", "Distinct Lyndon factors", DistinctFormula(),
                "Section 5, p. 8: “Let L(w) denote the number of distinct Lyndon factors in a word w.” Taking the image of the occurrence set before its cardinality counts equal factor lists once. Single letters and the whole Lyndon word are included. Section 6, p. 9 gives aaabaaabaab with seven distinct Lyndon factors and aababababab with eight.",
                AssessedProvenance.FromLiterature(Source)),
            Node("christoffel", "Lower Christoffel words", ChristoffelFormula(),
                "Section 5, p. 8: “The so-called Christoffel word of slope p/q beginning with the letter a is the unique Sturmian Lyndon word over {a, b} of length q containing p occurrences of the letter b, given by:” followed by aPal(v)b. Here a = 0 < 1 = b, the denominator is n, and the lower mechanical word uses natural-number floor division and truncated subtraction. The parameters used in the question satisfy 0 < p < n and Nat.Coprime p n. The formula reproduces the source's slopes 3/11, 5/11, and 11/28.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Open Problem 1", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "Section 6, p. 9: “Is it true that the minimum number of distinct Lyndon factors over all Lyndon words of the same length is attained by at least one Christoffel word of that length?” The proposition is the affirmative assertion for every n ≥ 2, with competitors over every finite ordered alphabet Fin k. The count is of distinct contiguous factors, including single letters and the whole word.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A negative answer at length 506", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Let U = aabaabab, V = aabab, v = ababbababbabbababbabb, and replace each a in v by UUV and each b by UUVV. The resulting word has length 506 and sixteen distinct Lyndon factors. A suffix comparison certifies that it is Lyndon. Compressed intervals of rejected suffixes certify the upper count, and sixteen distinct occurrences certify the lower count. For each positive numerator less than 506 and coprime to 506, seventeen distinct Lyndon-factor occurrences certify the Christoffel lower bound. Thus every Christoffel competitor has at least seventeen distinct factors. The argument does not determine the global minimum or the first counterexample length. Glen's 2018 41ACCMCC talk, slide 19, announces an affirmative answer; that announcement conflicts with this counterexample, and its proof is unavailable in the supplied material. The source's Theorem 8 concerns the Christoffel family alone and does not require the assertion refuted here.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("glen-simpson-smyth-2017-lyndon-factors-open-problem-1"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("gss-minimum-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
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

    private static Formula ChristoffelFormula()
    {
        Formula p = F.Id("p"), n = F.Id("n"), i = F.Id("i");
        Formula val = Parenthesized(Seq(i, Colon, Sp, Nats()));
        Formula lhs = Call("Nat.div", new Formula.Binary(
            Parenthesized(new Formula.Binary(val, FormulaBinaryOperator.Add, D(1))), FormulaBinaryOperator.Multiply, p), n);
        Formula rhs = Call("Nat.div", new Formula.Binary(val, FormulaBinaryOperator.Multiply, p), n);
        Formula test = Equal(Call("Nat.sub", lhs, rhs), D(1));
        Formula conditional = Seq(Named("if"), Sp, Parenthesized(test), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0));
        return Disp(All(p, Nats(), All(n, Nats(), Equal(Call("christoffel", p, n),
            Lam(i, Fin(n), conditional)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), p = F.Id("p"), k = F.Id("k"), w = F.Id("w");
        Formula comparison = All(k, Nats(), All(w, Fn(Fin(n), Fin(k)),
            Arrow(Call("IsLyndon", Call("List.ofFn", w)),
                Le(Call("distinctLyndon", Call("christoffel", p, n)), Call("distinctLyndon", w)))));
        return All(n, Nats(), Arrow(Le(D(2), n), Some(p, Nats(),
            And(Lt(D(0), p), And(Lt(p, n), And(Call("Nat.Coprime", p, n), comparison))))));
    }
}
