using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GaussianQuotient;

internal sealed class OkadaPreMergedNonPalindromicDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/okada2020merged");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Almost strictly pre-fitting tuples of width at least three give pre-merged Gaussian determinants that are not almost palindromic.",
        H("Almost palindromicity of pre-merged Gaussian determinants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("almost-palindromic"),
                DeclarationHandle.Create(Prefix + "IsAlmostPalindromic"),
                H("A palindrome after zero coefficients are omitted"),
                StatementSource.FromAuthor(Disp(AlmostPalindromicDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Sort the finite support of the integer polynomial f by increasing natural degree, "
                    + "and list its coefficients in that order. IsAlmostPalindromic applies "
                    + "List.Palindrome to this list. By List.Palindrome.iff_reverse_eq, this is "
                    + "equivalent to equality with its reverse. The coercion DFunLike.coe turns the finitely "
                    + "supported coefficient map into a function from natural degrees to integers. "
                    + "The empty list makes the zero polynomial almost palindromic. "
                    + "This is the integer-coefficient form of the definition for rational polynomials "
                    + "in arXiv:2003.02112v2, phases.tex, lines 8503–8512."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pre-merged"),
                DeclarationHandle.Create(Prefix + "preMerged"),
                H("The pre-merged difference of Gaussian products"),
                StatementSource.FromAuthor(Disp(PreMergedDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural tuples a and b of length μ, subtract the Gaussian product with "
                    + "a in reverse order from the product with a in its original order. "
                    + "Fin.rev sends index i to μ − 1 − i; all indices begin at zero. "
                    + "The Gaussian polynomial gauss has integer coefficients. The definition itself "
                    + "allows every μ and every pair of natural tuples, without monotonicity assumptions. "
                    + "It specializes the source's pre-merged determinant to unit weights, unit base "
                    + "shifts, zero degree shift, and a common indeterminate. The base shift factors "
                    + "are then one. See phases.tex, lines 755–762, 3508–3519, 5942–5958, and 6005–6048."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The assertion for every width at least three"),
                StatementSource.FromAuthor(Disp(Iff(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For μ at least three, a and b are strictly increasing natural tuples, and "
                    + "every entry of a is at most every entry of b. The latter condition is "
                    + "equivalent, for these tuples, to the last entry of a being at most the first "
                    + "entry of b. These are precisely the almost strictly pre-fitting tuples of "
                    + "phases.tex, lines 8337–8346. The proposition is the unit-parameter conjecture "
                    + "on non-almost-palindromicity in lines 8770–8779, with the Gaussian difference "
                    + "regarded as an integer polynomial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The second and penultimate coefficients disagree"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix μ, a and b satisfying the hypotheses. Gaussian symmetry gives diagonal "
                        + "value one. The Gaussian recurrence gives constant coefficient one whenever "
                        + "the lower index does not exceed the upper index. Its linear coefficient is one when "
                        + "the lower index is positive and strictly smaller than the upper index.")),
                    Paragraph(Text(
                        "For a natural n, write (X)ₙ for the product of 1 − Xʰ over 1 ≤ h ≤ n. "
                        + "Induction using the Gaussian hook identity gives "
                        + "gauss(n,k) (X)ₖ (X)ₙ₋ₖ = (X)ₙ for k ≤ n. "
                        + "Let t = b(0) − a(μ − 1). Strict increase, the cross inequalities and μ ≥ 3 "
                        + "give b(i) − a(i) ≥ t + 2 for every i. For reversed a, the difference at "
                        + "index zero is t, and every other difference is at least t + 2. "
                        + "All these differences are natural subtraction.")),
                    Paragraph(Text(
                        "Write a0 and b0 for the original and reversed Gaussian products, respectively. "
                        + "Multiplying the factorial identity over the indices, reindexing the "
                        + "a-factorials by Equiv.prod_comp with Fin.revPerm, and cancelling gives "
                        + "a0 ∏ᵢ (X)ᵦ₍ᵢ₎₋ₐ₍ᵢ₎ = b0 ∏ᵢ (X)ᵦ₍ᵢ₎₋ₐ₍Fin.rev i₎. "
                        + "The cancelled polynomial is nonzero because its constant coefficient is one.")),
                    Paragraph(Text(
                        "Work in the quotient of ℤ[X] by the ideal generated by X^(t + 3). "
                        + "There X is nilpotent, each (X)ₙ is a unit, and its image is independent "
                        + "of n once n ≥ t + 2. The original difference-factorials therefore have "
                        + "product (X)ₜ₊₂^μ, while the reversed ones have product "
                        + "(X)ₜ (X)ₜ₊₂^(μ − 1). Since "
                        + "(X)ₜ₊₂ = (X)ₜ (1 − X^(t + 1))(1 − X^(t + 2)), "
                        + "unit cancellation gives b0 = a0 (1 − X^(t + 1))(1 − X^(t + 2)) "
                        + "in this quotient.")),
                    Paragraph(Text(
                        "Put p = preMerged(a,b), r = t + 1, and let the natural number c be μ "
                        + "if a(0) > 0 and μ − 1 otherwise. The constant coefficient of a0 is one. "
                        + "The coefficient of degree one in a product of factors with constant "
                        + "coefficient one is the sum of their linear coefficients: apply the "
                        + "finite-product derivative identity derivative_prod_finset and take the "
                        + "constant coefficient. Thus the linear coefficient of a0 "
                        + "is (c : ℤ). If a(0) = 0, precisely the first factor contributes zero "
                        + "instead of one. The quotient identity now gives p.coeff(r) = 1, "
                        + "p.coeff(r + 1) = (c : ℤ) + 1, and p.coeff(n) = 0 for every n < r.")),
                    Paragraph(Text(
                        "Next, induction on the Gaussian recurrence proves that gauss(n,k) is "
                        + "monic, has natural degree k(n − k), and equals its polynomial reverse "
                        + "when k ≤ n. The dual Gaussian recurrence identifies the reflected sum "
                        + "in the induction step. The library's monic-product and degree identities, "
                        + "and reverse_mul_of_domain via Finset.prod_induction, extend these "
                        + "properties to products. Thus a0 "
                        + "has natural degree d = ∑ᵢ a(i)(b(i) − a(i)), and b0 has natural degree "
                        + "e = ∑ᵢ a(Fin.rev i)(b(i) − a(Fin.rev i)).")),
                    Paragraph(Text(
                        "To compare these degrees, cast every tuple entry from ℕ to ℤ. "
                        + "For each i, the product of the integer differences "
                        + "((a(i) : ℤ) − (a(Fin.rev i) : ℤ)) and "
                        + "((b(i) : ℤ) − (b(Fin.rev i) : ℤ)) is nonnegative: the two cast tuples "
                        + "are monotone, so the library's monovariation inequality applies. "
                        + "Summing and reindexing by Equiv.sum_comp with Fin.revPerm gives "
                        + "2((d : ℤ) − (e : ℤ)). "
                        + "At index zero both differences are at most −2, so this sum is at least "
                        + "four. Consequently e + 2 ≤ d in ℕ.")),
                    Paragraph(Text(
                        "The last entry a(μ − 1) is at least two, and "
                        + "b(μ − 1) − a(μ − 1) is at least t + 2. Its contribution to d gives d ≥ t + 4. "
                        + "The leading coefficient of a0 is one; reversal equates its coefficient "
                        + "at d − 1 with its linear coefficient (c : ℤ). Since e + 2 ≤ d, "
                        + "subtracting b0 changes neither coefficient. Hence p has natural degree "
                        + "d, with coefficients one at d and (c : ℤ) at d − 1.")),
                    Paragraph(Text(
                        "Finally c is positive and r + 1 < d − 1. In the increasing list of "
                        + "degrees in the support of p, the first two entries must be r and r + 1, "
                        + "and the last two must be d − 1 and d. Indeed, the coefficients at these "
                        + "four degrees are nonzero, none occur below r or above d, and the pairs "
                        + "are adjacent natural degrees. If the coefficient list satisfied "
                        + "List.Palindrome, List.Palindrome.iff_reverse_eq would identify its "
                        + "reverse with itself. Comparing index one with List.getElem?_reverse "
                        + "would then equate its second entry (c : ℤ) + 1 with its penultimate "
                        + "entry (c : ℤ). This is impossible, so p is not almost palindromic."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("okada-2020-premerged-determinant-nonpalindromic"),
                    ResolutionKind.Proved)))));

    private static Formula AlmostPalindromicDefinition()
    {
        var f = F.Id("f");
        var relation = LambdaOf("x1", Naturals(), LambdaOf("x2", Naturals(),
            LE(X("x1"), X("x2"))));
        var sorted = At(Qualified("Finset", "sort"),
            At(Qualified("Polynomial", "support"), f), relation);
        var coefficients = Typed(At(Qualified("DFunLike", "coe"),
            At(Qualified("Polynomial", "coeff"), f)),
            new Formula.TypeArrow(Naturals(), Integers()));
        var values = At(Qualified("List", "map"), coefficients, sorted);
        return All("f", Polynomials(), Iff(LocalCall("IsAlmostPalindromic", f),
            At(Qualified("List", "Palindrome"), values)));
    }

    private static Formula PreMergedDefinition() => All("μ", Naturals(),
        All("a", TupleType(), All("b", TupleType(),
            Eq(Typed(LocalCall("preMerged", F.Id("a"), F.Id("b")), Polynomials()),
                Sub(GaussianProduct(false), GaussianProduct(true))))));

    private static Formula GaussianProduct(bool reversed)
    {
        var i = F.Id("i");
        var index = reversed ? At(Qualified("Fin", "rev"), i) : i;
        var factor = At(Qualified("D5", "S3", "Combinatorics", "CylindricPartition",
            "LiUncuDefs", "gauss"), At(F.Id("b"), i), At(F.Id("a"), index));
        return Seq(new Formula.Subscript(Prod, Typed(i, FinOf(Mu))), Sp, Parenthesized(factor));
    }

    private static Formula ClaimBody()
    {
        var cross = All("i", FinOf(Mu), All("j", FinOf(Mu),
            LE(At(F.Id("a"), F.Id("i")), At(F.Id("b"), F.Id("j")))));
        var conclusion = new Formula.Not(Parenthesized(LocalCall("IsAlmostPalindromic",
            LocalCall("preMerged", F.Id("a"), F.Id("b")))));
        var hypotheses = Imp(LE(D(3), Mu),
            Imp(At(Qualified("StrictMono"), F.Id("a")),
                Imp(At(Qualified("StrictMono"), F.Id("b")), Imp(cross, conclusion))));
        return All("μ", Naturals(), All("a", TupleType(), All("b", TupleType(), hypotheses)));
    }

    private static Formula X(string name) => name switch
    {
        "μ" => Mu,
        "x1" => Seq(F.Id("x"), D(1)),
        "x2" => Seq(F.Id("x"), D(2)),
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(part switch
            {
                "D5" => Seq(F.Id("D"), D(5)),
                "S3" => Seq(F.Id("S"), D(3)),
                _ => F.Id(part),
            });
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Polynomials() => At(Qualified("Polynomial"), Integers());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula TupleType() => new Formula.TypeArrow(FinOf(Mu), Naturals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
