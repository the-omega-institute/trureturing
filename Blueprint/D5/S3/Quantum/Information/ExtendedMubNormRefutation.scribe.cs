using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ExtendedMubNormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/ExtendedMubNormRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/rotundo2023entropic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The doubly stochastic matrix I/2 + J/6 in dimension three satisfies the spectral condition of the extended MUB conjecture at mu = lambda = 2/3, but a nonzero real vector gives a mixed norm ratio strictly above the predicted norm.",
        H("A counterexample to the extended MUB norm conjecture"),
        Blocks(
            Node("stochastic", "Doubly stochastic matrices", StochasticFormula(),
                "Membership in Mathlib's doublyStochastic over the reals means nonnegative entries and every row sum and column sum equal to one. Fin(d) indexes rows and columns by 0, ..., d - 1.",
                "DoublyStochastic", AssessedProvenance.FromLiterature(Source)),
            Node("singular", "The second largest singular value", SigmaFormula(),
                "For d >= 2, sigma2 is the nonnegative square root of the eigenvalue at index 1 in the descending, multiplicity-preserving eigenvaluesZero list of the Hermitian Gram matrix C* C. Here C* is conjugate transpose, which equals transpose over the reals. The index is the Fin(card(Fin(d))) element with value 1; the definition extends by zero when d <= 1, outside the conjecture's domain. The operator ite selects its second argument when its first argument holds and its third argument otherwise.",
                "sigma2", AssessedProvenance.FromLiterature(Source)),
            Node("norm", "Ordinary finite real lp norms", LpFormula(),
                "For positive finite p this expression is the ordinary lp norm, without normalizing counting measure. Powers use Real.rpow. In the theorem, the expression is identified with the norm on Mathlib's PiLp(ENNReal.ofReal(p)) by PiLp.norm_eq_sum.",
                "lpNorm", AssessedProvenance.FromLiterature(Source)),
            Node("ratios", "All nonzero-vector norm ratios", RatiosFormula(),
                "The set contains the output q-norm divided by the input p-norm for every nonzero real vector; signs of coordinates are unrestricted. Matrix multiplication acts on column vectors.",
                "ratios", AssessedProvenance.FromRepo()),
            Node("operator", "The mixed operator norm", OpFormula(),
                "The supremum of the ratio set is the ordinary real mixed operator norm for p, q >= 1. The proof bounds the ratio set using the continuous linear map between finite PiLp spaces and its operator norm. The conjecture only uses exponents greater than one.",
                "opNorm", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1: extended MUB regime", ClaimFormula(),
                "Conjecture 1 (arXiv:2303.11382v1, p. 2): \"(Extended MUB regime). Let C⁽²⁾ be a doubly stochastic matrix. Its norm is equal to that of C⁽²⁾_MUB, i.e. it is given by eq. (7), as long as (1−μ)/μ (1−λ)/λ ≥ σ₂², where σ₂ is the second largest singular value of C⁽²⁾.\" Equation (7) reads log ||C⁽²⁾_MUB||_(1/μ → 1/(1−λ)) = (1−λ−μ) log d. The encoding uses C for C⁽²⁾, d >= 2, and 0 < mu, lambda < 1, with ordinary real-vector norms; val(d) is the coercion of the natural dimension to the reals. Equation (5) in the source allows complex vectors; the real vector used below belongs to that larger domain as well, so its strict lower bound also rules out the source's proposed complex norm value. No equality between real and complex operator norms is needed for this counterexample.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Node("result", "The predicted norm equality fails", Disp(new Formula.Not(F.Id("claim"))),
                "Set d = 3, C = I/2 + J/6, x = (4,1,1), and mu = lambda = 2/3. The matrix is doubly stochastic. Its Gram matrix is I/4 + J/4, with descending eigenvalues (1,1/4,1/4), so sigma2(C) = 1/2 and the spectral condition holds with equality. The input exponent is 3/2 and the output exponent is 3. Since Cx = (3,3/2,3/2), the input norm cubed is 100 and the output norm cubed is 135/4. The norm ratio cubed is therefore 27/80 > 1/3, whereas the conjectured value 3^(-1/3) has cube 1/3. Boundedness of the ratio set makes this ratio a lower bound for its supremum, contradicting the predicted equality. This argument supplies a lower bound, without asserting that x maximizes the ratio; it concerns the arXiv norm statement rather than the journal's entropic reformulation.",
                "result", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("mixnorm-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula ExistsIn(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula value, Formula domain) => Rel(value, FormulaRelationOperator.MemberOf, domain);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula d) => Call("Fin", d);
    private static Formula Vectors(Formula d) => Seq(FinOf(d), Sp, To, Sp, Reals());
    private static Formula Matrices(Formula d) => Call("Matrix", FinOf(d), FinOf(d), Reals());
    private static Formula Norm(Formula p, Formula x) => Call("lpNorm", p, x);
    private static Formula SigmaTwo(Formula c) => Call("sigma2", c);
    private static Formula Action(Formula c, Formula x) => Call("mulVec", c, x);

    private static Formula StochasticFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C");
        return Disp(All(d, Naturals(), All(c, Matrices(d),
            Iff(Call("DoublyStochastic", c), Member(c, Call("doublyStochastic", Reals(), FinOf(d)))))));
    }

    private static Formula SigmaFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C");
        Formula gram = Mul(Pow(c, Star), c);
        Formula root = Seq(Sqrt, Grp(Call("eigenvaluesZero", gram, D(1))));
        return Disp(All(d, Naturals(), All(c, Matrices(d),
            Equal(SigmaTwo(c), Call("ite", Lt(D(1), d), root, D(0))))));
    }

    private static Formula LpFormula()
    {
        Formula d = F.Id("d"), p = F.Id("p"), x = F.Id("x"), i = F.Id("i");
        Formula sum = Seq(new Formula.Subscript(Sum, Member(i, FinOf(d))), Sp,
            Pow(new Formula.Absolute(new Formula.Apply(x, [i])), p));
        return Disp(All(d, Naturals(), All(p, Reals(), All(x, Vectors(d),
            Equal(Norm(p, x), Pow(Parenthesized(sum), Div(D(1), p)))))));
    }

    private static Formula RatiosFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C"), p = F.Id("p"), q = F.Id("q"),
            x = F.Id("x"), r = F.Id("r");
        Formula nonzero = Rel(x, FormulaRelationOperator.NotEqual, D(0));
        Formula value = Div(Norm(q, Action(c, x)), Norm(p, x));
        Formula set = Seq(OpenBrace, r, Sp, Colon, Sp, Reals(), Sp, Mid, Sp,
            ExistsIn(x, Vectors(d), And(nonzero, Equal(r, value))), CloseBrace);
        return Disp(All(d, Naturals(), All(c, Matrices(d), All(p, Reals(), All(q, Reals(),
            Equal(Call("ratios", c, p, q), set))))));
    }

    private static Formula OpFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C"), p = F.Id("p"), q = F.Id("q");
        return Disp(All(d, Naturals(), All(c, Matrices(d), All(p, Reals(), All(q, Reals(),
            Equal(Call("opNorm", c, p, q), Call("sSup", Call("ratios", c, p, q))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C"), mu = Mu, lam = LambdaLower;
        Formula spectral = Le(Pow(SigmaTwo(c), D(2)),
            Mul(Div(Sub(D(1), mu), mu), Div(Sub(D(1), lam), lam)));
        Formula equality = Equal(Call("opNorm", c, Div(D(1), mu), Div(D(1), Sub(D(1), lam))),
            Pow(Call("val", d), Sub(Sub(D(1), lam), mu)));
        Formula body = All(d, Naturals(), All(c, Matrices(d), All(mu, Reals(), All(lam, Reals(),
            Implies(Le(D(2), d), Implies(Call("DoublyStochastic", c),
                Implies(Lt(D(0), mu), Implies(Lt(mu, D(1)), Implies(Lt(D(0), lam),
                    Implies(Lt(lam, D(1)), Implies(spectral, equality)))))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
