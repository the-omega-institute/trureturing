using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class NoisyWernerHolevoLindbladEmbeddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/roofehkarimipour2024wernerholevo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the interval from zero to two thirds, the noisy qutrit Werner-Holevo channel is a GKSL exponential exactly at zero noise.",
        H("Lindblad embeddability of the noisy Werner-Holevo channel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("werner-holevo"),
                DeclarationHandle.Create(Prefix + "wernerHolevo"),
                H("The noisy qutrit Werner-Holevo map"),
                StatementSource.FromAuthor(Disp(ChannelDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (lambdax), TeX line 153, combines the identity channel with the qutrit Werner-Holevo channel. "
                    + "The formula acts on all complex three by three matrices, using the ordinary transpose and matrix trace. "
                    + "The real parameter x is included in the complex scalars by Complex.ofReal. "
                    + "The source takes x between zero and one; the displayed linear map is defined for every real x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gksl-generator"),
                DeclarationHandle.Create(Prefix + "IsGKSLGenerator"),
                H("Finite GKSL generators"),
                StatementSource.FromAuthor(Disp(GeneratorDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A complex-linear generator has a Hermitian Hamiltonian H and a finite family V of jump matrices. "
                    + "Its Hamiltonian part is minus the imaginary unit times the commutator with H. "
                    + "Each jump contributes conjugation by V followed by subtraction of half the anticommutator with its adjoint product. "
                    + "The natural number m may be zero. This specifies the meaning of Lindbladian dynamics in the question at TeX line 249."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("generator-exponential"),
                DeclarationHandle.Create(Prefix + "generatorExp"),
                H("The exponential of a generator"),
                StatementSource.FromAuthor(Disp(ExponentialDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The matrix-unit basis identifies a complex-linear endomorphism of the matrix space with a nine by nine complex matrix. "
                    + "Take the ordinary matrix exponential and transport it back through the inverse algebra equivalence. "
                    + "The exponential is evaluated at time one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Embeddability on the remaining interval"),
                StatementSource.FromAuthor(Disp(Equivalence(Typed(Local("claim"), Qualified("Prop")), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The question at TeX line 249 concerns parameters between zero and two thirds, including both endpoints. "
                    + "For every such real x, existence of a finite GKSL generator whose exponential equals the noisy channel is equivalent to x being zero. "
                    + "Equality here is equality of linear maps on the entire complex matrix space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exactly zero noise is Lindblad embeddable"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The zero endomorphism is a GKSL generator: take m equal to zero, the zero Hamiltonian, and the empty jump family. "
                        + "Its exponential and the channel at x equal to zero are both the identity map.")),
                    Paragraph(Text(
                        "Every generator exponential is invertible, since its matrix exponential is a unit and the algebra equivalence preserves units. "
                        + "An eigenvector of G with eigenvalue μ is therefore an eigenvector of its exponential with eigenvalue exp(μ); "
                        + "this follows by passing to coordinates in the matrix-unit basis and back.")),
                    Paragraph(Text(
                        "For an idempotent linear map P commuting with G, restrict G to the range W of P. "
                        + "The restriction is obtained by composing the inclusion of W, G, and the range restriction of P. "
                        + "If the exponential of G times P equals b times P for a positive real b, each eigenvalue μ of this restriction satisfies exp(μ) = b. "
                        + "Taking the complex norm gives exp(Re μ) = b, hence Re μ = log b. "
                        + "The characteristic polynomial splits over the complex numbers, so summing its roots gives real trace equal to the complex dimension of W times log b. "
                        + "Cyclicity of the linear-map trace identifies this trace with the real trace of G composed with P; "
                        + "the trace of an idempotent is the dimension of its range.")),
                    Paragraph(Text(
                        "At x equal to two thirds the nonzero diagonal matrix with diagonal entries 1, minus 1, and 0 is sent to zero. "
                        + "Thus the endpoint channel cannot equal any generator exponential, which is injective.")),
                    Paragraph(Text(
                        "Let P send X to (X + Xᵀ)/2 minus trace(X) times the identity divided by 3, "
                        + "and let Q send X to (X − Xᵀ)/2. "
                        + "Write s(G) and a(G) for the real endomorphism traces of G composed with P and Q, respectively. "
                        + "For the Hamiltonian commutator, s minus five times a is zero. "
                        + "For a single jump matrix V, the same difference is twice the sum of the squared complex norms of "
                        + "V₀₀ − V₁₁, V₀₀ − V₂₂, and V₁₁ − V₂₂, plus three times the sum of the squared complex norms of "
                        + "V₀₁ + V₁₀, V₀₂ + V₂₀, and V₁₂ + V₂₁. "
                        + "These identities follow by expanding the trace in the matrix-unit basis and the matrix entries of the two projections. "
                        + "Linearity of trace and nonnegativity of every squared norm imply s(G) − 5a(G) is nonnegative for every GKSL generator.")),
                    Paragraph(Text(
                        "The generator commutes with its exponential. Every GKSL generator has trace(G(X)) equal to zero: "
                        + "cyclicity of the matrix trace cancels both the commutator and each jump term. "
                        + "The noisy channel fixes the identity. If x is nonzero and its channel equals the exponential of G, "
                        + "commutation makes G applied to the identity a fixed matrix of that channel. "
                        + "Its trace is zero, and the equations for its transposed entries force every entry to vanish. "
                        + "Applying commutation to an arbitrary matrix then shows that G commutes with transposition. "
                        + "Together with trace zero and G applied to the identity equal to zero, this proves that G commutes with both P and Q.")),
                    Paragraph(Text(
                        "Direct matrix-entry calculations show that P and Q are idempotent with traces 5 and 3. "
                        + "The noisy channel acts on their ranges by b = 1 − 3x/2 and c = 1 − x/2, respectively, "
                        + "as in the source's spectral formulas at TeX lines 236–247. "
                        + "For x strictly between zero and two thirds both scalars are positive. "
                        + "The preceding restriction argument gives s(G) = 5 log b and a(G) = 3 log c.")),
                    Paragraph(Text(
                        "Strict Bernoulli inequality with increment minus x/2 and exponent 3 gives b strictly less than c cubed. "
                        + "Monotonicity of the logarithm and the logarithm of a power yield 5 log b strictly less than 15 log c. "
                        + "This contradicts s(G) − 5a(G) being nonnegative. "
                        + "For an x in the closed interval, any nonzero x is positive and lies either in this interior or at the excluded endpoint. "
                        + "Both alternatives are impossible, and the zero generator supplies the converse."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("roofeh-karimipour-2024-werner-holevo-lindblad-embedding"),
                    ResolutionKind.Proved)))));

    private static Formula ChannelDefinition()
    {
        Formula x = X("x");
        Formula scalar = Typed(At(Qualified("Complex", "ofReal"), x), Complexes());
        Formula identity = Typed(Qualified("LinearMap", "id"), Endomorphisms());
        Formula transpose = At(Qualified("LinearEquiv", "toLinearMap"),
            At(Qualified("Matrix", "transposeLinearEquiv"), FinOf(D(3)), FinOf(D(3)), Complexes(), Complexes()));
        Formula trace = At(Qualified("Matrix", "traceLinearMap"), FinOf(D(3)), Complexes(), Complexes());
        Formula traceIdentity = At(Qualified("LinearMap", "smulRight"), trace, Typed(D(1), Matrices()));
        Formula half = Div(scalar, Typed(D(2), Complexes()));
        return All("x", Reals(), Equal(Typed(LocalCall("wernerHolevo", x), Endomorphisms()),
            Add(Subtract(Smul(Subtract(Typed(D(1), Complexes()), scalar), identity), Smul(half, transpose)),
                Smul(half, traceIdentity))));
    }

    private static Formula GeneratorDefinition()
    {
        Formula g = X("G"), h = X("H"), v = At(X("V"), X("k")), x = X("X");
        Formula adjoint = At(Qualified("Matrix", "conjTranspose"), v);
        Formula commutator = Subtract(Multiply(h, x), Multiply(x, h));
        Formula jump = Subtract(Multiply(Multiply(v, x), adjoint),
            Smul(Div(Typed(D(1), Complexes()), Typed(D(2), Complexes())),
                Add(Multiply(Multiply(adjoint, v), x), Multiply(x, Parenthesized(Multiply(adjoint, v))))));
        Formula action = Equal(At(g, x),
            Add(Smul(new Formula.Negate(Qualified("Complex", "I")), commutator),
                SumOver("k", FinOf(X("m")), jump)));
        Formula generators = Some("m", Naturals(), Some("H", Matrices(),
            Some("V", Arrow(FinOf(X("m")), Matrices()),
                Conjunction(At(Qualified("Matrix", "IsHermitian"), h), All("X", Matrices(), action)))));
        return All("G", Endomorphisms(),
            Equivalence(Typed(LocalCall("IsGKSLGenerator", g), Qualified("Prop")), generators));
    }

    private static Formula ExponentialDefinition()
    {
        Formula basis = At(Qualified("Matrix", "stdBasis"), Complexes(), FinOf(D(3)), FinOf(D(3)));
        Formula equivalence = At(Qualified("LinearMap", "toMatrixAlgEquiv"), basis);
        Formula exponential = At(Qualified("NormedSpace", "exp"), At(Parenthesized(equivalence), X("G")));
        Formula inverse = At(Qualified("AlgEquiv", "symm"), equivalence);
        return All("G", Endomorphisms(), Equal(Typed(LocalCall("generatorExp", X("G")), Endomorphisms()),
            At(Parenthesized(inverse), exponential)));
    }

    private static Formula ClaimBody()
    {
        Formula x = X("x"), g = X("G");
        Formula interval = At(Qualified("Set", "Icc"), Typed(D(0), Reals()),
            Div(Typed(D(2), Reals()), Typed(D(3), Reals())));
        Formula existence = Some("G", Endomorphisms(),
            Conjunction(LocalCall("IsGKSLGenerator", g), Equal(LocalCall("generatorExp", g), LocalCall("wernerHolevo", x))));
        return All("x", Reals(), Arrow(new Formula.Relation(x, FormulaRelationOperator.MemberOf, interval),
            Equivalence(existence, Equal(x, Typed(D(0), Reals())))));
    }

    private static Formula Matrices() => At(Qualified("Matrix"), FinOf(D(3)), FinOf(D(3)), Complexes());
    private static Formula Endomorphisms() => At(Qualified("Module", "End"), Complexes(), Matrices());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "NoisyWernerHolevoLindbladEmbedding", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
}
