using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class CorrelationTopEigenvectorWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/CorrelationTopEigenvectorWeight.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Estimation/stepanovherrmannguhr2021correlation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the remaining correlation domain, matrices whose top eigenvectors have smaller weight exist in every sufficiently large dimension exactly when c is less than sigma.",
        H("Top eigenvector weights on the remaining correlation domain"),
        Blocks(
            Node("is-correlation", "IsCorrelation", "Correlation matrices", CorrelationFormula(),
                "A real matrix is a correlation matrix when it is positive semidefinite and every diagonal entry is one. "
                    + "Matrix.PosSemidef includes symmetry over the real scalars. These are conditions (i)–(iii) in the source's TeX, lines 141–146. "
                    + "The predicate is defined for every natural dimension, including zero."),
            Node("mean-corr", "meanCorr", "Mean off-diagonal correlation", MeanFormula(),
                "The mean is the sum of the entries strictly below the diagonal, multiplied by two divided by n(n−1), as in the source's TeX, lines 176–179. "
                    + "Nat.cast explicitly includes the natural dimension in the real scalars. Real division is total, so the same definition gives zero in dimensions zero and one."),
            Node("std-corr", "stdCorr", "Standard deviation of the correlations", StandardDeviationFormula(),
                "The standard deviation is the real square root of the mean squared off-diagonal entry minus the square of the mean correlation, as in the source's TeX, lines 180–184. "
                    + "Both sums use the strict lower triangle. The definition is total for arbitrary real matrices: real square root is zero for a negative argument."),
            Node("delta", "delta", "The normalized diagonal vector", DeltaFormula(),
                "The source's diagonal vector has every coordinate equal to the reciprocal square root of n (TeX, lines 154–157). "
                    + "Function.const forms the constant coordinate family, and WithLp.toLp places it in real Euclidean space. "
                    + "Its squared norm is one when n is positive; at dimension zero the vector is the unique empty vector."),
            Node("satisfies-w-gap", "SatisfiesWGap", "A strict gap above each top eigenvector weight", WeightGapFormula(),
                "For every orthonormal eigenbasis v with eigenvalue function l, each index i whose eigenvalue is maximal has another index j with strictly larger squared projection on delta n. "
                    + "This is the source's basis-independent meaning of a matrix satisfying w₁ < w_max (TeX, lines 877–879), with every maximal index allowed in place of a fixed ordering. "
                    + "DFunLike.coe applies the basis to an index; WithLp.ofLp makes the coordinate functions in the eigenvector equation explicit. "
                    + "The predicate itself does not assume that the matrix is a correlation matrix."),
            Node("domain-d", "domainD", "The domain left between the two known regions", DomainFormula(),
                "The domain consists of positive c and σ inside the unit disk, outside both A₁ and A₂ from the source's TeX, lines 510–518. "
                    + "Thus neither c ≥ 1/2 nor σ < c holds, and neither σ > √3 c nor c < σ < 1−c holds. "
                    + "In particular, σ = c and the non-strict wedge boundaries are retained whenever the other defining inequalities hold."),
            Node("claim", "claim", "The eventual-existence question", Equivalence(Local("claim"), ClaimBody()),
                "Question III.5 asks for correlation matrices at each point of the remaining domain in sufficiently large dimensions (source TeX, lines 525–527). "
                    + "Here sufficiently large means that there is a natural threshold m such that every natural n ≥ m admits a matrix a with exactly mean c, standard deviation σ and the strict weight gap. "
                    + "The threshold may depend on c and σ, and the matrix may depend on n. The displayed proposition specifies that this existence holds exactly when c < σ."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Eventual existence holds exactly above the diagonal"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, the defining inequalities for the domain give 0 < c < 1/2 and c ≤ σ. "
                            + "Either σ = c, or 1−c ≤ σ ≤ √3 c; the inequality c²+σ² < 1 holds in both cases. "
                            + "We exclude the diagonal σ = c before constructing matrices in the second case.")),
                    Paragraph(Text(
                        "In dimensions zero and one the mean is zero, and in dimension two the standard deviation is zero. "
                            + "These dimensions cannot have mean and standard deviation both equal to a positive c. "
                            + "For n ≥ 3, choose an orthonormal eigenbasis v of a correlation matrix a, write l for its eigenvalues, and set μ j = l j−1 and w j = ⟨v j, delta n⟩². "
                            + "The trace and squared Frobenius norm give Σ μ j = 0 and Σ (μ j)² = n(n−1)(c²+σ²). "
                            + "Parseval gives nonnegative weights with Σ w j = 1. Expanding the Rayleigh quotient of delta n gives Σ μ j w j = (n−1)c. "
                            + "If the strict weight gap holds and i has maximal eigenvalue, another weight is larger than w i, so w i < 1/2.")),
                    Paragraph(Text(
                        "Choose j with the largest μ j among indices other than i. Bounding the weighted sum on those indices and using w i < 1/2 gives 2(n−1)c ≤ μ i+μ j. "
                            + "Apply Cauchy–Schwarz to the remaining n−2 entries, whose sum is −(μ i+μ j), and use (μ i−μ j)² ≥ 0 for the two selected entries. "
                            + "Together these imply n(μ i+μ j)² ≤ 2(n−2)Σ (μ k)². "
                            + "Substitution yields 2(n−1)c² ≤ (n−2)(c²+σ²), hence c² < σ² because c > 0. "
                            + "Thus a matrix with σ = c cannot satisfy the gap in any dimension. "
                            + "If eventual existence held while c < σ failed, the domain inequality c ≤ σ would force equality; taking n = m would contradict this obstruction.")),
                    Paragraph(Text(
                        "For the converse suppose c < σ. Set L = (σ²−(1−c)²)/(σ²+(1−c)²), U = (σ²−c²)/(c²+σ²), and x = (L+min(c,U))/2. "
                            + "The domain inequalities give 0 ≤ L < x < min(c,U) < 1/2. "
                            + "Consequently a = σ/√(1−x²) and b = c−a x satisfy a > 0, b > 0, 1−a−b > 0 and 2c < a+b. "
                            + "The bounds x < c, x > L and x < U respectively ensure the last three strict inequalities after squaring positive quantities.")),
                    Paragraph(Text(
                        "For each natural n, choose the integer k nearest to n(1+√x)/2 and put z = ((2k−n)²−n)/(n(n−1)), with n and k included in the real scalars in these expressions. "
                            + "The rounding error is at most one half, so k/n tends to (1+√x)/2 and z tends to x. "
                            + "Continuity of square root and division then shows that, for every sufficiently large n, a = σ/√(1−z²), b = c−a z and d = 1−a−b are positive. "
                            + "The same limit argument gives n ≥ 3, 0 < k < n, 2k ≠ n, −1 < z < 1, and 2(n−1)c < (n−2)(a+b). "
                            + "The integer inequalities use the natural dimension cast to the integers.")),
                    Paragraph(Text(
                        "Let s have k entries equal to one and the remaining entries equal to minus one, let u be the all-ones vector, and form the matrix dI+a ssᵀ+b uuᵀ. "
                            + "There are n(n−1)/2 entries strictly below the diagonal. Apply the pair representation in the first projection of SignPairUStatisticMoments.sign_pair_u_statistic_moments to the corresponding integer units, taking its product-law mean parameter to be zero. "
                            + "The sign sum is 2k−n; swapping the triangular indices and clearing the nonzero denominator gives the lower-triangle sum of s i s j as ((2k−n)²−n)/2. "
                            + "Positive coefficients make the matrix positive semidefinite, and s i squared equal to one makes its diagonal equal to d+a+b = 1. "
                            + "The two lower-triangle identities give mean a z+b = c and second moment a²+b²+2abz. "
                            + "Subtracting c² leaves a²(1−z²) = σ², whose nonnegative square root is σ.")),
                    Paragraph(Text(
                        "It remains to prove the strict weight gap in every eigenbasis of this matrix. "
                            + "For an arbitrary orthonormal eigenbasis v with eigenvalues l, put μ j = l j−d, e j = ⟨v j,u⟩ and f j = ⟨v j,s⟩. "
                            + "Taking inner products of the eigenvector equations gives diagonal μ = a ffᵀ+b eeᵀ. "
                            + "Factor this diagonal matrix through two columns: its rank is at most two, so at most two μ j are nonzero. "
                            + "Its diagonal identity gives μ j = a(f j)²+b(e j)² ≥ 0, and μ j = 0 forces e j = 0. "
                            + "Parseval gives Σ (e j)² = Σ (f j)² = n, and summing the diagonal identity gives Σ μ j = n(a+b). "
                            + "The sign sum gives ⟨u,s⟩ = 2k−n; applying the matrix to u therefore yields Σ μ j(e j)² = a(2k−n)²+bn². "
                            + "The strict inequality 2(n−1)c < (n−2)(a+b), together with c = a z+b, is exactly 2Σ μ j(e j)² < (Σ μ j)(Σ (e j)²).")),
                    Paragraph(Text(
                        "Fix any maximal eigenvalue index i. The strict inequality rules out having only one nonzero μ j, so there is another nonzero index j distinct from i, and all the sums reduce to these two indices. "
                            + "It follows that (μ i−μ j)((e i)²−(e j)²) < 0. Maximality gives μ j ≤ μ i, hence (e i)² < (e j)². "
                            + "Since delta n is u multiplied by the positive reciprocal square root of n, multiplying by its square preserves this strict inequality and gives the required comparison of weights. "
                            + "The common threshold from the limit estimates therefore supplies the required matrix in every n ≥ m, proving the reverse implication."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CorrelationFormula() => MatrixBinders(Equivalence(LocalCall("IsCorrelation", X("c")),
        Conjunction(At(Qualified("Matrix", "PosSemidef"), X("c")),
            All("i", FinOf(X("n")), Equal(At(X("c"), X("i"), X("i")), Typed(D(1), Reals()))))));

    private static Formula MeanFormula() => MatrixBinders(Equal(
        Typed(LocalCall("meanCorr", X("c")), Reals()), Multiply(MeanFactor(), LowerSum(At(X("c"), X("i"), X("j"))))));

    private static Formula StandardDeviationFormula() => MatrixBinders(Equal(
        Typed(LocalCall("stdCorr", X("c")), Reals()), Root(Subtract(
            Multiply(MeanFactor(), LowerSum(Square(At(X("c"), X("i"), X("j"))))),
            Square(LocalCall("meanCorr", X("c")))))));

    private static Formula DeltaFormula() => All("n", Naturals(), Equal(
        Typed(LocalCall("delta", X("n")), Euclidean()),
        At(Qualified("WithLp", "toLp"), D(2),
            At(Qualified("Function", "const"), FinOf(X("n")), At(Qualified("Inv", "inv"), Root(NatReal(X("n"))))))));

    private static Formula WeightGapFormula()
    {
        Formula coordinates = Typed(At(Qualified("WithLp", "ofLp"), BasisVector(X("j"))), Arrow(FinOf(X("n")), Reals()));
        Formula eigenvectors = All("j", FinOf(X("n")), Equal(
            At(Qualified("Matrix", "mulVec"), X("c"), coordinates),
            At(Qualified("SMul", "smul"), At(X("l"), X("j")), coordinates)));
        Formula top = All("j", FinOf(X("n")), LE(At(X("l"), X("j")), At(X("l"), X("i"))));
        Formula gap = Some("j", FinOf(X("n")), Conjunction(NotEqual(X("j"), X("i")),
            Less(Square(Inner(BasisVector(X("i")), LocalCall("delta", X("n")))),
                Square(Inner(BasisVector(X("j")), LocalCall("delta", X("n")))))));
        return MatrixBinders(Equivalence(LocalCall("SatisfiesWGap", X("c")),
            All("v", At(Qualified("OrthonormalBasis"), FinOf(X("n")), Reals(), Euclidean()),
                All("l", Arrow(FinOf(X("n")), Reals()),
                    Arrow(eigenvectors, All("i", FinOf(X("n")), Arrow(top, gap)))))));
    }

    private static Formula DomainFormula() => All("c", Reals(), All("σ", Reals(),
        Equivalence(LocalCall("domainD", X("c"), X("σ")), Conjunction(
            Conjunction(Less(D(0), X("c")), Conjunction(Less(D(0), X("σ")),
                Less(Add(Square(X("c")), Square(X("σ"))), D(1)))),
            Conjunction(Not(Disjunction(LE(Divide(D(1), D(2)), X("c")), Less(X("σ"), X("c")))),
                Not(Disjunction(Less(Multiply(Root(Typed(D(3), Reals())), X("c")), X("σ")),
                    Conjunction(Less(X("c"), X("σ")), Less(X("σ"), Subtract(D(1), X("c")))))))))));

    private static Formula ClaimBody() => All("c", Reals(), All("σ", Reals(),
        Arrow(LocalCall("domainD", X("c"), X("σ")), Equivalence(
            Some("m", Naturals(), All("n", Naturals(), Arrow(LE(X("m"), X("n")),
                Some("a", MatrixType(), Conjunction(LocalCall("IsCorrelation", X("a")),
                    Conjunction(Equal(LocalCall("meanCorr", X("a")), X("c")),
                        Conjunction(Equal(LocalCall("stdCorr", X("a")), X("σ")), LocalCall("SatisfiesWGap", X("a"))))))))),
            Less(X("c"), X("σ"))))));

    private static Formula MatrixBinders(Formula body) => All("n", Naturals(), All("c", MatrixType(), body));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("n")), FinOf(X("n")), Reals());
    private static Formula Euclidean() => At(Qualified("EuclideanSpace"), Reals(), FinOf(X("n")));
    private static Formula MeanFactor() => Divide(D(2), Multiply(NatReal(X("n")), Subtract(NatReal(X("n")), D(1))));
    private static Formula LowerSum(Formula body) => SumOver("i", FinOf(X("n")),
        Seq(new Formula.Subscript(Sum, Seq(Typed(X("j"), FinOf(X("n"))), Comma, Sp, Less(X("j"), X("i")))),
            Sp, Parenthesized(body)));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula BasisVector(Formula index) => At(Qualified("DFunLike", "coe"), X("v"), index);
    private static Formula Inner(Formula left, Formula right) => At(Qualified("inner"), Reals(), left, right);
    private static Formula Local(string name) => Qualified("D5", "S3", "Estimation", "CorrelationTopEigenvectorWeight", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name == "σ" ? SigmaLower : F.Id(name);
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
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula NatReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Root(Formula value) => At(Qualified("Real", "sqrt"), value);
}
