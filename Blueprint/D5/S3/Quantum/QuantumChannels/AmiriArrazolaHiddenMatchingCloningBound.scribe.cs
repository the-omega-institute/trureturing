using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class AmiriArrazolaHiddenMatchingCloningBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/amiriarrazola2016hiddenmatching");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hidden-matching cloning has mean marginal fidelity at most one half plus 1/n.",
        H("The hidden-matching cloning bound"), Blocks(
            Paragraph(Text(
                "The input dimension is n, and the two output factors both have dimension n. "
                    + "A bit string is a function from Fin n to Fin 2. The coordinates 0 through n − 1 "
                    + "relabel the source's coordinates 1 through n. QuantumChannel is the complex "
                    + "completely positive trace-preserving linear-map carrier. The output coordinates "
                    + "are ordered Y × Z; partialTraceRight traces out Z and partialTraceLeft traces out Y. "
                    + "All inverses and divisions in these formulas are scalar operations. The theorem "
                    + "requires n ≥ 2, so sqrt n and n are nonzero.")),
            Node("phi", "phi", "The hidden-matching vector", PhiFormula(),
                "Equation (4), p. 3: “In hidden matching QRGs the set of possible inputs is the set of all "
                    + "n-bit strings, each chosen with equal probability, where n is an even number. "
                    + "Alice encodes her input into the n-dimensional pure state” followed by "
                    + "|φ_x⟩ = (1/√n) ∑ᵢ₌₁ⁿ (−1)^{x_i}|i⟩. "
                    + "The displayed coordinate function is this vector in the computational basis."),
            Node("rho", "rho", "The pure input matrix", RhoFormula(),
                "Section II A 2, p. 6: “In reference to Fig. 4, we refer to these states as the white states, "
                    + "and start by considering a single such state, φ_{xⁱ} := |φ_{xⁱ}⟩⟨φ_{xⁱ}|, contained in the coin.” "
                    + "“For simplicity, we drop the superscript on the n-bit strings xⁱ in all that follows.” "
                    + "Matrix.vecMulVec forms that outer product, and CStarMatrix.ofMatrix places "
                    + "the matrix in the channel's ordered matrix carrier."),
            Node("eta", "eta", "The first marginal", MarginalFormula(false),
                "Equation (11), p. 7: “where η_x = Tr_Z[Ψ(|φ_x⟩⟨φ_x|)] and "
                    + "τ_x = Tr_Y[Ψ(|φ_x⟩⟨φ_x|)].” The first expression traces out the second output factor."),
            Node("tau", "tau", "The second marginal", MarginalFormula(true),
                "Equation (11), p. 7: “where η_x = Tr_Z[Ψ(|φ_x⟩⟨φ_x|)] and "
                    + "τ_x = Tr_Y[Ψ(|φ_x⟩⟨φ_x|)].” The second expression traces out the first output factor."),
            Node("mean-fidelity", "meanFidelity", "The mean marginal fidelity", MeanFormula(),
                "Equation (11), p. 7: “We want to find the channel that maximises” "
                    + "F̄ = 2⁻ⁿ ∑ₓ (⟨φ_x|η_x|φ_x⟩ + ⟨φ_x|τ_x|φ_x⟩)/2. "
                    + "The sum ranges over all functions Fin n → Fin 2, exactly 2ⁿ inputs. "
                    + "Complex.re gives the real scalar order on the two expectations."),
            Node("claim", "claim", "The dimension-uniform assertion", Equal(Named("claim"), ClaimBody()),
                "Equation (21), p. 8, states F̄ ≤ 1/2 + 1/n. The following sentence, p. 9, is: "
                    + "“which we have verified numerically for n ≤ 14 and we conjecture holds for any n. "
                    + "From now on, we simply assume that n ≤ 14.” The dimensions here are all positive "
                    + "even dimensions, expressed by 2 ≤ n and Even n, and the channel is arbitrary."),
            Describe.Lean(
                DescribeId.Create("aa1610-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The mean fidelity bound in every positive even dimension"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Averaging four binary signs leaves precisely the index patterns in which "
                            + "each coordinate has even multiplicity. This evaluates the performance "
                            + "operator as 1/(2n²) times a nonnegative symmetric matrix L on triples.")),
                    Paragraph(Text(
                        "For a triple (a,b,c), assign weight 2(n−1) when a=b=c, weight 2 when b=c "
                            + "and a differs, and weight n otherwise. Every weight is positive for n ≥ 2. "
                            + "The weighted row sum of L is at most (n+2) times this weight. The scaled "
                            + "complex quadratic row estimate then bounds its quadratic form by "
                            + "(n+2) times the squared Euclidean norm.")),
                    Paragraph(Text(
                        "The finite Kraus representation decomposes the input-first Choi matrix "
                            + "into outer products. Its trace is n by trace preservation. The tensor "
                            + "Choi pairing identifies the averaged two-marginal objective with the "
                            + "performance-operator trace. Summing the quadratic bound over the "
                            + "Kraus vectors gives (n+2)/(2n) = 1/2 + 1/n. No symmetry or covariance "
                            + "condition on the channel is used.")),
                    Paragraph(Text(
                        "This theorem removes the n ≤ 14 restriction for equation (21). It does "
                            + "not assert a uniform attaining channel or the paper's further protocol-security results.")))))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("aa1610-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula QCall(string owner, string name, params Formula[] arguments) => At(Qualified(owner, name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Times, b));
    private static Formula BitsOf(Formula n) => Arrow(FinOf(n), FinOf(D(2)));
    private static Formula Channel(Formula n) => Call("QuantumChannel", FinOf(n), Product(FinOf(n), FinOf(n)));
    private static Formula All(Formula v, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(v, t), Comma, Sp, Parenthesized(b));
    private static Formula Lambda(Formula v, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(v, t), Comma, Sp, Parenthesized(b)));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Inv(Formula a) => new Formula.Power(Parenthesized(a), Seq(Minus, D(1)));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula SumOver(Formula v, Formula t, Formula b) =>
        Seq(new Formula.Subscript(Sum, Typed(v, t)), Sp, Parenthesized(b));
    private static Formula Input(Formula n, Formula x) => Call("phi", n, x);
    private static Formula Expectation(Formula n, Formula channel, Formula x, string marginal) =>
        QCall("Complex", "re", Call("dotProduct", Call("star", Input(n, x)),
            QCall("Matrix", "mulVec", Call(marginal, n, channel, x), Input(n, x))));

    private static Formula PhiFormula()
    {
        var n = F.Id("n"); var x = F.Id("x"); var i = F.Id("i");
        return All(n, Nats(), All(x, BitsOf(n), Equal(Input(n, x), Lambda(i, FinOf(n),
            Mul(Inv(Typed(QCall("Real", "sqrt", Typed(n, Reals())), Complexes())),
                Pow(Typed(Seq(Minus, D(1)), Complexes()), At(Qualified("Fin", "val"), At(x, i))))))));
    }
    private static Formula RhoFormula()
    {
        var n = F.Id("n"); var x = F.Id("x");
        return All(n, Nats(), All(x, BitsOf(n), Equal(Call("rho", n, x),
            QCall("CStarMatrix", "ofMatrix", QCall("Matrix", "vecMulVec", Input(n, x), Call("star", Input(n, x)))))));
    }
    private static Formula MarginalFormula(bool left)
    {
        var n = F.Id("n"); var channel = F.Id("N"); var x = F.Id("x");
        var output = At(Seq(channel, Dot, Named("toCompletelyPositiveMap")), Call("rho", n, x));
        var raw = At(Seq(Qualified("CStarMatrix", "ofMatrix"), Dot, Named("symm")), output);
        return All(n, Nats(), All(channel, Channel(n), All(x, BitsOf(n),
            Equal(Call(left ? "tau" : "eta", n, channel, x), Call(left ? "partialTraceLeft" : "partialTraceRight", raw)))));
    }
    private static Formula MeanFormula()
    {
        var n = F.Id("n"); var channel = F.Id("N"); var x = F.Id("x");
        return All(n, Nats(), All(channel, Channel(n), Equal(Call("meanFidelity", n, channel),
            Mul(Div(D(1), Pow(Typed(D(2), Reals()), n)), SumOver(x, BitsOf(n),
                Div(Add(Expectation(n, channel, x, "eta"), Expectation(n, channel, x, "tau")), D(2)))))));
    }
    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var channel = F.Id("N");
        return All(n, Nats(), Implies(LE(D(2), n), Implies(Call("Even", n),
            All(channel, Channel(n), LE(Call("meanFidelity", n, channel),
                Add(Div(Typed(D(1), Reals()), D(2)), Div(D(1), Typed(n, Reals()))))))));
    }
}
