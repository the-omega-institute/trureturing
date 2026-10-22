using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Polynomials;

internal sealed class MiskaUlasSigmaThreeBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/miskaulas2022sigma");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integer family refutes the degree-six symmetric-product bound.",
        H("The first bound of Miska–Ulas Conjecture 4.8 is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("miska-ulas-sigma-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Conjecture 4.8"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff,
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Page 16: “Let n ∈ N≥4 and suppose that m ∈ N satisfies m = σ_3(X_n) = σ_n(X_n). Then m ≤ (1/12)(3021n⁶ − 77575n⁵ + 920361n⁴ − 6235705n³ + 24764202n² − 53664304n + 48986640) and x_n ≤ (1/12)(27n⁴ − 190n³ + 471n² − 500n + 216).”")),
                    Paragraph(Text("Page 1: “Let n ∈ N≥3 and for given k ≤ n consider the k-th symmetric polynomial σ_k(x_1, . . . , x_n) = Σ_{i_1<i_2<...<i_k} x_{i_1} · · · x_{i_k}.” Page 2: “By a solution of (1) we mean a sequence X_n = (x_1, . . . , x_n) satisfying the condition x_i ≤ x_{i+1} for i = 1, . . . , n − 1”, in positive integers.")),
                    Paragraph(Text("The tuple is indexed by Fin n, starting at zero. MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ k) is the sum of products over k-element subsets. Monotone X expresses the source's nondecreasing order. The last index is the element of Fin n with value n − 1; its proof of being less than n is omitted in the display and follows from 4 ≤ n. The polynomial arithmetic and all displayed casts use ℚ."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miska-ulas-sigma-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For k ≥ 7 put n = k + 4, c = 3 σ₂(1ᵏ) + 8k + 7, and let Y consist of k ones followed by 2, k + 3, c. Put d = σ₃(Y) and append d to Y. The identity σ₂(Y) + 1 = 2(k + 3)c makes the resulting tuple solve σ₃ = σₙ. Its entries are positive and nondecreasing. The difference between its product and the proposed degree-six bound is (27/4) k(k − 1)(k − 2)(k − 3)(k − 4)(k − 5)(k − 6), positive for k ≥ 7. The proof specializes this family to n = 11.")),
                    Paragraph(Text("The last coordinate on this family equals the proposed quartic bound. Thus this family contradicts the first bound while attaining equality in the second. The universal second bound remains open. The source's results about σ₂ = σₙ concern a different equation and are unaffected by this refutation of its final conjecture about σ₃."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("miska-ulas-2022-sigma-three-conjecture-4-8"),
                    ResolutionKind.Refuted))),
        []));

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rats()));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, byte exponent) => new Formula.Power(value, D(exponent));
    private static Formula Elementary(Formula n, Formula x, Formula degree) =>
        Call("MvPolynomial.eval", x, Call("MvPolynomial.esymm", Call("Fin", n), Nats(), degree));

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), x = F.Id("X"), i = F.Id("i"), m = F.Id("m"), nq = Cast(n);
        Formula bound = Add(Sub(Add(Sub(Add(Sub(Mul(D(3, 0, 2, 1), Pow(nq, 6)),
            Mul(D(7, 7, 5, 7, 5), Pow(nq, 5))), Mul(D(9, 2, 0, 3, 6, 1), Pow(nq, 4))),
            Mul(D(6, 2, 3, 5, 7, 0, 5), Pow(nq, 3))), Mul(D(2, 4, 7, 6, 4, 2, 0, 2), Pow(nq, 2))),
            Mul(D(5, 3, 6, 6, 4, 3, 0, 4), nq)), D(4, 8, 9, 8, 6, 6, 4, 0));
        Formula coordinate = Add(Sub(Add(Sub(Mul(D(2, 7), Pow(nq, 4)),
            Mul(D(1, 9, 0), Pow(nq, 3))), Mul(D(4, 7, 1), Pow(nq, 2))),
            Mul(D(5, 0, 0), nq)), D(2, 1, 6));
        Formula factor = new Formula.Fraction(D(1), D(1, 2));
        Formula lastIndex = Seq(Langle, Sp, Sub(n, D(1)), Rangle);
        Formula conclusion = new Formula.Logic(
            Parenthesized(Leq(Cast(m), Mul(factor, Parenthesized(bound)))), FormulaLogicOperator.And,
            Parenthesized(Leq(Cast(App(x, lastIndex)), Mul(factor, Parenthesized(coordinate)))));
        Formula positive = All(i, Call("Fin", n), new Formula.Relation(D(0), FormulaRelationOperator.LessThan, App(x, i)));
        return All(n, Nats(), Arrow(Leq(D(4), n),
            All(x, Seq(Call("Fin", n), Sp, To, Sp, Nats()), Arrow(positive, Arrow(Call("Monotone", x),
                All(m, Nats(), Arrow(Equal(m, Elementary(n, x, D(3))),
                    Arrow(Equal(m, Elementary(n, x, n)), conclusion))))))));
    }
}
