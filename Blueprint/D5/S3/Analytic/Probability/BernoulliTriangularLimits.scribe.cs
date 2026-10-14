using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BernoulliTriangularLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Divergent Bernoulli row variances give central and local limits for polynomial coefficient laws.",
        H("Bernoulli Triangular Limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rowmean"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMean"),
                H("rowMean"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Equal(Call("rowMean", V("p")), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mean of the unshifted Bernoulli row."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rowvariance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowVariance"),
                H("rowVariance"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Equal(Call("rowVariance", V("p")), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Multiply(Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)), Parenthesized(Subtract(new Formula.Number(1), Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the Bernoulli variances."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rowmass"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMass"),
                H("rowMass"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), All("k", Integer, Equal(Call("rowMass", V("p"), V("k")), Seq(new Formula.Subscript(Sum, Seq(V("x"), Colon, Sp, new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("Bool")))))), Sp, Parenthesized(Call("ite", Equal(Parenthesized(Seq(Parenthesized(Seq(Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(new Formula.Apply(Qualified("Bool", "toNat"), [new Formula.Apply(V("x"), [V("i")])]))), Colon, Sp, Nat)), Colon, Sp, Integer)), V("k")), Call("bernoulliWeight", V("p"), V("x")), new Formula.Number(0)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer-lattice mass of the sum of Boolean coordinates. The full natural-number sum is cast to the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoulli-array-uniform-lattice-limit"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_array_uniform_lattice_limit"),
                H("bernoulli_array_uniform_lattice_limit"),
                StatementSource.FromAuthor(Disp(All("m", new Formula.TypeArrow(Nat, Nat), All("p", All("n", Nat, new Formula.TypeArrow(Call("Fin", new Formula.Apply(V("m"), [V("n")])), Seq(Operatorname, Grp(V("unitInterval"))))), Imp(Call("Tendsto", LambdaFormula("n", Nat, Call("rowVariance", new Formula.Apply(V("p"), [V("n")]))), V("atTop"), V("atTop")), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("k", Integer, Rel(new Formula.Absolute(Subtract(Multiply(new Formula.Apply(Qualified("Real", "sqrt"), [Call("rowVariance", new Formula.Apply(V("p"), [V("n")]))]), Call("rowMass", new Formula.Apply(V("p"), [V("n")]), V("k"))), new Formula.Apply(Call("gaussianPDFReal", new Formula.Number(0), new Formula.Number(1)), [new Formula.Fraction(Subtract(Parenthesized(Seq(V("k"), Colon, Sp, Real)), Call("rowMean", new Formula.Apply(V("p"), [V("n")]))), new Formula.Apply(Qualified("Real", "sqrt"), [Call("rowVariance", new Formula.Apply(V("p"), [V("n")]))]))]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")])))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/bender1973limits")),
                Blocks(Paragraph(Text("Fourier inversion and dominated convergence give a uniform local limit on the integer lattice. The sum of the Boolean coordinates is centered by rowMean."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-lattice-limit-to-floor"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.uniform_lattice_limit_to_floor"),
                H("uniform_lattice_limit_to_floor"),
                StatementSource.FromAuthor(Disp(All("a", new Formula.TypeArrow(Nat, new Formula.TypeArrow(Integer, Real)), All("M", new Formula.TypeArrow(Nat, Real), All("S", new Formula.TypeArrow(Nat, Real), Imp(And(Call("Tendsto", V("S"), V("atTop"), V("atTop")), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("k", Integer, Rel(new Formula.Absolute(Subtract(Multiply(new Formula.Apply(V("S"), [V("n")]), new Formula.Apply(V("a"), [V("n"), V("k")])), new Formula.Apply(Call("gaussianPDFReal", new Formula.Number(0), new Formula.Number(1)), [new Formula.Fraction(Subtract(Parenthesized(Seq(V("k"), Colon, Sp, Real)), new Formula.Apply(V("M"), [V("n")])), new Formula.Apply(V("S"), [V("n")]))]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")])))), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("t", Real, Rel(new Formula.Absolute(Subtract(Multiply(new Formula.Apply(V("S"), [V("n")]), new Formula.Apply(V("a"), [V("n"), FloorFormula(Add(new Formula.Apply(V("M"), [V("n")]), Multiply(V("t"), new Formula.Apply(V("S"), [V("n")]))))])), new Formula.Apply(Call("gaussianPDFReal", new Formula.Number(0), new Formula.Number(1)), [V("t")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")]))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniform continuity of the Gaussian density transfers a uniform lattice limit to the literal integer floor of M(n)+t*S(n). The rounding error is less than 1/S(n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.mu"),
                H("mu"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), Equal(Call("mu", V("f")), new Formula.Fraction(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), Call("derivative", V("f"))]), new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")])))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Theorem 4.2, page 9, defines μₙ = fₙ′(1)/fₙ(1). The first logarithmic derivative of f evaluated at one is the coefficient-law mean."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sigmasq"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq"),
                H("sigmaSq"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), Equal(Call("sigmaSq", V("f")), Subtract(Add(new Formula.Fraction(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), Call("derivative", Call("derivative", V("f")))]), new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")])), Call("mu", V("f"))), new Formula.Power(Parenthesized(Call("mu", V("f"))), new Formula.Number(2))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Theorem 4.2, page 9, defines σₙ² = fₙ″(1)/fₙ(1) + μₙ − μₙ². The variance is the normalized second derivative at one plus the mean minus its square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sigma"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigma"),
                H("sigma"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), Equal(Call("sigma", V("f")), new Formula.Apply(Qualified("Real", "sqrt"), [Call("sigmaSq", V("f"))]))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("The standard deviation σₙ is the nonnegative square root of the variance in Section 4, pages 8–9. The encoding uses Real.sqrt sigmaSq."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prob"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.prob"),
                H("prob"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), All("k", Integer, Equal(Call("prob", V("f"), V("k")), Call("ite", Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, V("k")), new Formula.Fraction(new Formula.Apply(Qualified("Polynomial", "coeff"), [V("f"), new Formula.Apply(Qualified("Int", "toNat"), [V("k")])]), new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")])), new Formula.Number(0))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Section 4, page 9, defines p(n,k) = a(n,k)/∑ⱼ₌₀ⁿ a(n,j). For a nonnegative integer k, the mass is coefficient k.toNat divided by f(1); for negative k it is zero. Polynomial evaluation at one sums the coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("std-normal-cdf"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalCDF"),
                H("StatLean.HypothesisTesting.stdNormalCDF"),
                StatementSource.FromAuthor(Disp(All("t", Real, Equal(new Formula.Apply(StatLeanName("stdNormalCDF"), [V("t")]), new Formula.Apply(StatLeanName("normalCDF"), [D(0), D(1), V("t")]))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier")),
                Blocks(Paragraph(Text("StatLean.HypothesisTesting.normalCDF(m,v,t) is (gaussianReal m v (Set.Iic t)).toReal. Its specialization at m=0 and v=1 is the source expression (1/√(2π))∫₋∞ᵗ exp(−x²/2) dx."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("std-normal-pdf"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF"),
                H("StatLean.HypothesisTesting.stdNormalPDF"),
                StatementSource.FromAuthor(Disp(All("t", Real, Equal(new Formula.Apply(StatLeanName("stdNormalPDF"), [V("t")]), new Formula.Fraction(Call("exp", new Formula.Negate(new Formula.Fraction(new Formula.Power(Parenthesized(V("t")), D(2)), D(2)))), new Formula.Apply(Qualified("Real", "sqrt"), [Multiply(D(2), Pi)])))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier")),
                Blocks(Paragraph(Text("The density exp(−t²/2)/√(2π) equals the source expression (1/√(2π)) exp(−t²/2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("clt"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.CLT"),
                H("CLT"),
                StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(Nat, Call("Polynomial", Real)), IffFormula(Call("CLT", V("f")), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("t", Real, Rel(new Formula.Absolute(Subtract(Seq(new Formula.Subscript(Sum, Seq(V("k"), Sp, InMacro, Sp, Call("filter", LambdaFormula("k", Nat, Rel(Parenthesized(Seq(V("k"), Colon, Sp, Real)), FormulaRelationOperator.LessThanOrEqual, Add(Call("mu", new Formula.Apply(V("f"), [V("n")])), Multiply(V("t"), Call("sigma", new Formula.Apply(V("f"), [V("n")])))))), Call("range", Add(Call("natDegree", new Formula.Apply(V("f"), [V("n")])), new Formula.Number(1)))))), Sp, Parenthesized(Call("prob", new Formula.Apply(V("f"), [V("n")]), Parenthesized(Seq(V("k"), Colon, Sp, Integer))))), new Formula.Apply(StatLeanName("stdNormalCDF"), [V("t")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")]))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Section 4, page 8: “The coefficient a(n, k) is said to be asymptotically normal with mean μₙ and variance σₙ² by a central limit theorem if” limₙ→∞ supₜ∈ℝ |∑ₖ≤μₙ+tσₙ p(n,k) − (1/√(2π))∫₋∞ᵗ exp(−x²/2) dx| = 0. The central limit convention uses an epsilon bound uniform in the real threshold t. The range includes all natural indices through the polynomial degree. The normal CDF is StatLean.HypothesisTesting.stdNormalCDF."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("llt"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.LLT"),
                H("LLT"),
                StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(Nat, Call("Polynomial", Real)), IffFormula(Call("LLT", V("f")), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("t", Real, Rel(new Formula.Absolute(Subtract(Multiply(Call("sigma", new Formula.Apply(V("f"), [V("n")])), Call("prob", new Formula.Apply(V("f"), [V("n")]), FloorFormula(Add(Call("mu", new Formula.Apply(V("f"), [V("n")])), Multiply(V("t"), Call("sigma", new Formula.Apply(V("f"), [V("n")]))))))), new Formula.Apply(StatLeanName("stdNormalPDF"), [V("t")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")]))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Section 4, page 9: “The coefficient a(n, k) is said to be asymptotically normal with mean μₙ and variance σₙ² by a local limit theorem on the real set ℝ if” limₙ→∞ supₜ∈ℝ |σₙ p(n,⌊μₙ+tσₙ⌋) − (1/√(2π)) exp(−t²/2)| = 0. The local limit convention uses an epsilon bound uniform in t, with the literal integer floor of mu(f(n))+t*sigma(f(n)). The density is StatLean.HypothesisTesting.stdNormalPDF."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoullipgf"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulliPGF"),
                H("bernoulliPGF"),
                StatementSource.FromAuthor(Disp(All("p", Real, Equal(Call("bernoulliPGF", V("p")), Add(Call("C", Subtract(new Formula.Number(1), V("p"))), Multiply(Call("C", V("p")), V("X"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial of a Bernoulli variable is C(1-p)+C(p)*X."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.normalized"),
                H("normalized"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), Equal(Call("normalized", V("f")), Multiply(Call("C", new Formula.Power(Parenthesized(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")])), new Formula.Negate(Parenthesized(new Formula.Number(1))))), V("f")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization multiplies f by the constant inverse of its value at one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sigmasq-mul"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_mul"),
                H("sigmaSq_mul"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), All("h", Call("Polynomial", Real), Imp(And(Rel(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")]), FormulaRelationOperator.NotEqual, new Formula.Number(0)), Rel(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("h")]), FormulaRelationOperator.NotEqual, new Formula.Number(0))), Equal(Call("sigmaSq", Multiply(V("f"), V("h"))), Add(Call("sigmaSq", V("f")), Call("sigmaSq", V("h"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Variance adds under polynomial multiplication when both values at one are nonzero."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("sigmasq-c"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_C"),
                H("sigmaSq_C"),
                StatementSource.FromAuthor(Disp(All("c", Real, Equal(Call("sigmaSq", Call("C", V("c"))), new Formula.Number(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A constant polynomial has zero sigmaSq."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("sigmasq-x"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_X"),
                H("sigmaSq_X"),
                StatementSource.FromAuthor(Disp(Equal(Call("sigmaSq", Parenthesized(Seq(V("X"), Colon, Sp, Call("Polynomial", Real)))), new Formula.Number(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic shift X has zero variance."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("factorization-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.factorization_moments"),
                H("factorization_moments"),
                StatementSource.FromAuthor(Disp(All("f", Call("Polynomial", Real), All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Imp(Equal(Call("normalized", V("f")), Multiply(V("X"), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliPGF", Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real))))))), And(Rel(new Formula.Apply(Qualified("Polynomial", "eval"), [new Formula.Number(1), V("f")]), FormulaRelationOperator.NotEqual, new Formula.Number(0)), And(Equal(Call("mu", V("f")), Add(new Formula.Number(1), Call("rowMean", V("p")))), Equal(Call("sigmaSq", V("f")), Call("rowVariance", V("p"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A shifted Bernoulli factorization fixes the total mass, mean and variance of the normalized coefficient law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-polynomial-uniform-limits"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_polynomial_uniform_limits"),
                H("bernoulli_polynomial_uniform_limits"),
                StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(Nat, Call("Polynomial", Real)), All("m", new Formula.TypeArrow(Nat, Nat), All("p", All("n", Nat, new Formula.TypeArrow(Call("Fin", new Formula.Apply(V("m"), [V("n")])), Seq(Operatorname, Grp(V("unitInterval"))))), Imp(And(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, Equal(Call("normalized", new Formula.Apply(V("f"), [V("n")])), Multiply(V("X"), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Call("bernoulliPGF", Parenthesized(Seq(new Formula.Apply(V("p"), [V("n"), V("i")]), Colon, Sp, Real)))))))), V("atTop")]), Call("Tendsto", LambdaFormula("n", Nat, Call("rowVariance", new Formula.Apply(V("p"), [V("n")]))), V("atTop"), V("atTop"))), And(Call("CLT", V("f")), Call("LLT", V("f"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/bender1973limits")),
                Blocks(Paragraph(Text("For polynomial arrays with an eventual shifted Bernoulli factorization, variance divergence yields both the uniform central and local limits."))),
                DescribeRole.Theorem))));

    private static Formula StatLeanName(string name) =>
        Seq(Qualified("StatLean", "HypothesisTesting"), Dot, Operatorname, Grp(V(name)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula FloorFormula(Formula value) => Seq(Left, Lfloor, Sp, value, Right, Rfloor);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

}
