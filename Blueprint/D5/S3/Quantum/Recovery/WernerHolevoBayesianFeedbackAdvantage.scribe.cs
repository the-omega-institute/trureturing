using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class WernerHolevoBayesianFeedbackAdvantageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/HilbertOperators/rexitioskoueimancini2024bayesianfeedback");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bayesian feedback exceeds every two-step Markovian fidelity for the qutrit Werner–Holevo channel.",
        H("Bayesian feedback advantage for the qutrit Werner–Holevo channel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kraus-decomposition"),
                DeclarationHandle.Create(Module + ".IsKrausDecomposition"),
                H("Finite Kraus decompositions of the Werner–Holevo channel"),
                StatementSource.FromAuthor(Disp(KrausFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A family k indexed by Fin m is a Kraus decomposition when its operator sum agrees, "
                        + "on every complex three-by-three matrix x, with the Werner–Holevo map at the real parameter 1. "
                        + "That map sends x to one half of tr(x)I minus one half of the transpose of x. "
                        + "The adjoint in the operator sum is the conjugate transpose. The equality is required "
                        + "on all matrices, rather than only on density matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("markov-fidelity"),
                DeclarationHandle.Create(Module + ".markovFidelity"),
                H("Two-step Markovian entanglement fidelity"),
                StatementSource.FromAuthor(Disp(MarkovFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Markovian feedback corrects each step separately. The resulting branch operator is "
                        + "the product of the absolute values of the second and first Kraus operators, in that order. "
                        + "The fidelity is one ninth of the sum of squared real traces of those products. "
                        + "Here CFC.abs T is the positive square root of TᴴT. "
                        + "This is the two-step Markovian formula in EffOfBayesianFB.tex, lines 245–249, "
                        + "with dimension d equal to 3. The displayed real part makes the real-valued expression explicit. "
                        + "The definition accepts arbitrary finite matrix families; the comparison below assumes they represent the channel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bayes-fidelity"),
                DeclarationHandle.Create(Module + ".bayesFidelity"),
                H("Two-step Bayesian entanglement fidelity"),
                StatementSource.FromAuthor(Disp(BayesFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Bayesian feedback corrects the accumulated branch after the first correction. "
                        + "For outcomes a and b the matrix is k₂ b times the absolute value of k₁ a. "
                        + "Its trace norm is the real trace of the positive square root of its adjoint times itself. "
                        + "The fidelity sums the squares of these trace norms and divides by 9. "
                        + "This is EffOfBayesianFB.tex, lines 250–253, specialized to dimension 3. "
                        + "As with the Markovian expression, the definition itself imposes no Kraus-decomposition hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A strict Bayesian advantage"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First consider arbitrary finite Kraus decompositions K₁ and K₂ of the channel. "
                            + "For a single decomposition K, apply its operator-sum identity to xxᴴ and evaluate "
                            + "the quadratic form on the conjugate of x. The channel side is zero, while the sum side "
                            + "is the sum over a of |xᵀ(K a)x|². Every summand is nonnegative, so every quadratic form "
                            + "vanishes. Coordinate vectors give zero diagonal entries, and sums of two distinct "
                            + "coordinate vectors give opposite off-diagonal entries. Thus every K a is antisymmetric.")),
                    Paragraph(Text(
                        "Taking traces of the channel identity on matrix units gives the trace-preservation identity "
                            + "Σₐ(K a)ᴴ(K a) = I. Write A(z) for the matrix of the linear map y ↦ z × y. "
                            + "The antisymmetry gives K a = A(z a)/√2, with z a = √2((K a)₂₁,(K a)₀₂,(K a)₁₀). "
                            + "Substituting the cross-product matrices and comparing diagonal and "
                            + "off-diagonal entries yields Σₐ(z a)(z a)ᴴ = I. Hence both decompositions give such frames.")),
                    Paragraph(Text(
                        "For V = zzᴴ and c = ‖z‖², direct multiplication gives A(z)ᴴA(z) = cI − V "
                            + "and V² = cV. If z is nonzero, put r = ‖z‖. The matrix rI − r⁻¹V equals "
                            + "r⁻¹(cI − V), is positive semidefinite, and squares to cI − V. "
                            + "Uniqueness of the positive square root therefore gives "
                            + "|A(z)/√2| = (rI − r⁻¹zzᴴ)/√2. The zero vector gives the zero matrix separately.")),
                    Paragraph(Text(
                        "The rank-one trace identities are tr(zzᴴ) = ‖z‖² and "
                            + "tr(wwᴴzzᴴ) = (wᴴz)(zᴴw). Expanding the product of the two absolute values therefore gives, "
                            + "for nonzero w and z, tr(|A(w)/√2||A(z)/√2|) = (u + v/u)/2, "
                            + "where u = ‖w‖‖z‖ and v = |wᴴz|². Cauchy–Schwarz gives 0 ≤ v ≤ u², "
                            + "and consequently (u + v/u)² ≤ u² + 3v. Thus the squared real trace is at most "
                            + "(‖w‖²‖z‖² + 3|wᴴz|²)/4. The same bound holds when either vector is zero.")),
                    Paragraph(Text(
                        "Taking traces of each frame identity gives Σₐ‖z a‖² = Σᵦ‖w b‖² = 3. "
                            + "Contracting the second frame against a rank-one matrix gives "
                            + "Σᵦ|(w b)ᴴ(z a)|² = ‖z a‖², so the double sum of squared overlaps is 3. "
                            + "The double sum of products of squared norms is 9. Summing the preceding pairwise bound "
                            + "and multiplying by 1/9 gives markovFidelity K₁ K₂ ≤ (9 + 3·3)/36 = 1/2.")),
                    Paragraph(Text(
                        "For the existential assertion choose l₁ i = A(eᵢ)/√2 and l₂ j = A(wⱼ)/√2, "
                            + "where eᵢ are the three coordinate vectors and "
                            + "w₀ = (2,2,−1)/3, w₁ = (−1,2,2)/3, w₂ = (2,−1,2)/3. "
                            + "Expanding all matrix entries of the two operator sums shows that each equals "
                            + "the Werner–Holevo map. Both chosen families therefore satisfy IsKrausDecomposition.")),
                    Paragraph(Text(
                        "The first family's absolute values are (I − eᵢeᵢᴴ)/√2. For each i,j set "
                            + "p = I − eᵢeᵢᴴ, b = A(wⱼ)p and s = |Re(wⱼ)ᵢ|. The matrix "
                            + "root = s p/(2(1+s)) + bᴴb/(2(1+s)) is positive semidefinite: p = pᴴp, "
                            + "bᴴb is positive semidefinite, and both coefficients are nonnegative. "
                            + "For the nine pairs, direct entrywise calculation gives root² = (b/2)ᴴ(b/2) "
                            + "and Re tr(root) = (1+s)/2. Since l₂ j |l₁ i| = b/2, uniqueness of the "
                            + "positive square root identifies root with the absolute value of that branch.")),
                    Paragraph(Text(
                        "There are six entries with s = 2/3 and three with s = 1/3. Substitution in the "
                            + "Bayesian fidelity gives (6(5/6)² + 3(2/3)²)/9 = 11/18 > 1/2. "
                            + "The universal Markovian bound and these two three-operator decompositions give the two "
                            + "conjuncts of the assertion. This supplies a channel with a strict Bayesian advantage "
                            + "as requested in EffOfBayesianFB.tex, lines 910–911."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rexiti-oskouei-mancini-2024-werner-holevo-bayesian-feedback"),
                    ResolutionKind.Proved)))));

    private static Formula KrausFormula()
    {
        Formula term = Multiply(Multiply(At(X("k"), X("a")), X("x")),
            At(Qualified("Matrix", "conjTranspose"), At(X("k"), X("a"))));
        Formula channel = At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
            "NoisyWernerHolevoLindbladEmbedding", "wernerHolevo"), Typed(D(1), Reals()), X("x"));
        return All("m", Naturals(), All("k", Family(X("m")),
            Equivalence(LocalCall("IsKrausDecomposition", X("k")),
                All("x", MatrixType(), Equal(SumOver("a", FinOf(X("m")), term), channel)))));
    }

    private static Formula MarkovFormula()
    {
        Formula product = Multiply(At(Qualified("CFC", "abs"), At(X("k₂"), X("b"))),
            At(Qualified("CFC", "abs"), At(X("k₁"), X("a"))));
        Formula realTrace = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), product));
        return FidelityBinders(Equal(Typed(LocalCall("markovFidelity", X("k₁"), X("k₂")), Reals()),
            Multiply(RealFraction(1, 9), SumOver("a", FinOf(X("m₁")),
                SumOver("b", FinOf(X("m₂")), Square(realTrace))))));
    }

    private static Formula BayesFormula()
    {
        Formula product = Multiply(At(X("k₂"), X("b")),
            At(Qualified("CFC", "abs"), At(X("k₁"), X("a"))));
        Formula traceNorm = At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"),
            product);
        return FidelityBinders(Equal(Typed(LocalCall("bayesFidelity", X("k₁"), X("k₂")), Reals()),
            Multiply(RealFraction(1, 9), SumOver("a", FinOf(X("m₁")),
                SumOver("b", FinOf(X("m₂")), Square(traceNorm))))));
    }

    private static Formula ResultFormula()
    {
        Formula bound = FidelityBinders(Arrow(LocalCall("IsKrausDecomposition", X("k₁")),
            Arrow(LocalCall("IsKrausDecomposition", X("k₂")),
                LE(LocalCall("markovFidelity", X("k₁"), X("k₂")), RealFraction(1, 2)))));
        Formula advantage = Some("l₁", Family(D(3)), Some("l₂", Family(D(3)),
            Conjunction(LocalCall("IsKrausDecomposition", X("l₁")),
                Conjunction(LocalCall("IsKrausDecomposition", X("l₂")),
                    LT(RealFraction(1, 2), LocalCall("bayesFidelity", X("l₁"), X("l₂")))))));
        return Conjunction(bound, advantage);
    }

    private static Formula FidelityBinders(Formula body) => All("m₁", Naturals(), All("m₂", Naturals(),
        All("k₁", Family(X("m₁")), All("k₂", Family(X("m₂")), body))));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(D(3)), FinOf(D(3)), Complexes());
    private static Formula Family(Formula m) => Arrow(FinOf(m), MatrixType());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula LocalCall(string name, params Formula[] args) =>
        At(Qualified("D5", "S3", "Quantum", "Recovery", "WernerHolevoBayesianFeedbackAdvantage", name), args);
    private static Formula X(string name) => name switch
    {
        "m₁" => new Formula.Subscript(F.Id("m"), D(1)),
        "m₂" => new Formula.Subscript(F.Id("m"), D(2)),
        "k₁" => new Formula.Subscript(F.Id("k"), D(1)),
        "k₂" => new Formula.Subscript(F.Id("k"), D(2)),
        "l₁" => new Formula.Subscript(F.Id("l"), D(1)),
        "l₂" => new Formula.Subscript(F.Id("l"), D(2)),
        _ => F.Id(name),
    };
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
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula RealFraction(byte numerator, byte denominator) =>
        new Formula.Fraction(Typed(D(numerator), Reals()), Typed(D(denominator), Reals()));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Typed(D(2), Naturals()));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
