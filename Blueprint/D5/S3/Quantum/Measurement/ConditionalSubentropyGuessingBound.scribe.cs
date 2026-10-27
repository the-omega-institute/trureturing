using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ConditionalSubentropyGuessingBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/datta2014conditionalsubentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simplex-integral conditional subentropy of a classical-quantum state is bounded by guessing min-entropy.",
        H("Conditional subentropy and guessing"), Blocks(
            Node("C", CFormula(),
                "Equation (2), PDF page 2: \"Q(ρ) = ⟨H(M(ρ))⟩_M − C_n where C_n := 1/2 + 1/3 + … + 1/n.\" The sum runs from 2 through n, inclusive.", AssessedProvenance.FromLiterature(Source)),
            Node("simplexCoords", SimplexCoordsFormula(),
                "Equation (3), PDF page 2: \"this uniform measure (normalised to have total volume unity) is given by dx = (n − 1)! dx_1 … dx_{n−1}.\" The first n−1 coordinates are nonnegative and have sum at most one.", AssessedProvenance.FromLiterature(Source)),
            Node("simplex_volume", SimplexVolumeFormula(),
                "The standard simplex in n coordinates has volume equal to the reciprocal of n factorial.", AssessedProvenance.FromRepo()),
            Node("simplex_sum_boundary_null", SimplexSumBoundaryNullFormula(),
                "Every positive level set of the coordinate sum has zero volume.", AssessedProvenance.FromRepo()),
            Node("subentropySpectrum", SpectrumFormula(),
                "Equation (4), PDF page 2: \"Introducing η(y) := −y ln y, we then obtain a third expression for the subentropy from eq.(2): Q(ρ) = n ∫_{Δn} η(λ · x) dx − C_n.\" Real.negMulLog is η. The Lebesgue integral is multiplied by (n−1)!, as in equation (3).", AssessedProvenance.FromLiterature(Source)),
            Node("subentropy", SubentropyFormula(),
                "Equation (4), PDF page 2: \"Introducing η(y) := −y ln y, we then obtain a third expression for the subentropy from eq.(2): Q(ρ) = n ∫_{Δn} η(λ · x) dx − C_n.\" R supplies its real Hermitian eigenvalues, including zero and repeated eigenvalues.", AssessedProvenance.FromLiterature(Source)),
            Node("pGuess", GuessFormula(),
                "PDF page 9: \"p_guess(X|B) = max_{{E_x}:POVM} Σ_x p_x Tr(E_x ρ^x_B), where the maximization is over all possible POVMs: {E_x : E_x ≥ 0 ∀ x; Σ_x E_x = I}.\" A x is p_xρ_B^x. The supremum is over these finite-POVM scores.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Conjecture 2, PDF page 9: \"For a c-q state ρ_XB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ H_min(X|B) = − ln p_guess(X|B).\" Equation (13), PDF page 8: \"we define the conditional subentropy to be Q(A|B)_ρ := Q(ρ_AB) − Q(ρ_B)\". X and B are arbitrary finite types with decidable equality. A has positive semidefinite blocks of total trace one. Matrix.blockDiagonal A is the joint state, and the sum of A is its B marginal. Natural logarithms are used.", AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "The simplex integral equals the determinant-integral subentropy on positive semidefinite trace-one matrices. Gaussian radial decomposition proves this equality without a simple-spectrum assumption. Normalizing the nonzero blocks gives a probability ensemble; zero blocks contribute zero. The ensemble guessing bound gives the inequality.", AssessedProvenance.FromRepo(Source), true))));

    private static DocumentBlock.Describe Node(string name, Formula formula, string text, AssessedProvenance provenance, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("conditionalsubentropy-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Owner + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("datta-dorlas-jozsa-benatti-2014-conditional-subentropy-conjecture-2"),
                ResolutionKind.Proved) : null);

    private static Formula CFormula() => All("n", Natural,
        Eqn(Call("C", Id("n")), SumOver("k", Call("Finset.Icc", D(2), Id("n")), Divide(D(1), Typed(Id("k"), Real)))));
    private static Formula SimplexCoordsFormula()
    {
        Formula coordinates = Arrow(Call("Fin", Sub(Id("n"), D(1))), Real);
        Formula nonnegative = All("i", Call("Fin", Sub(Id("n"), D(1))), Leq(D(0), Apply(Id("y"), Id("i"))));
        Formula sumBound = Leq(SumOver("i", Call("Fin", Sub(Id("n"), D(1))), Apply(Id("y"), Id("i"))), D(1));
        return All("n", Natural, Eqn(Call("simplexCoords", Id("n")), SetOf("y", coordinates, And(nonnegative, sumBound))));
    }
    private static Formula SimplexVolumeFormula() => All("n", Natural,
        Eqn(Call("volume", Call("simplexCoords", Add(Id("n"), D(1)))),
            Pow(Typed(Call("Nat.factorial", Id("n")), ENNRealType), new Formula.Negate(D(1)))));
    private static Formula SimplexSumBoundaryNullFormula()
    {
        Formula coordinates = Arrow(Call("Fin", Id("n")), Real);
        Formula sum = SumOver("i", Call("Fin", Id("n")), Apply(Id("u"), Id("i")));
        Formula levelSet = SetOf("u", coordinates, Eqn(sum, Id("t")));
        return All("n", Natural, All("t", Real,
            Imp(Lt(D(0), Id("t")), Eqn(Call("volume", levelSet), D(0)))));
    }
    private static Formula SpectrumFormula()
    {
        Formula linear = SumOver("i", Call("Fin", Id("n")), Mul(Apply(Id("lam"), Id("i")), Call("D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.chart", Id("y"), Id("i"))));
        Formula integral = IntegralOver("y", Call("simplexCoords", Id("n")), Call("Real.negMulLog", linear));
        Formula rhs = Sub(Mul(Typed(Id("n"), Real), Parenthesized(Mul(Typed(Call("Nat.factorial", Sub(Id("n"), D(1))), Real), integral))), Call("C", Id("n")));
        return All("n", Natural, All("lam", Arrow(Call("Fin", Id("n")), Real), Eqn(Call("subentropySpectrum", Id("n"), Id("lam")), rhs)));
    }
    private static Formula SubentropyFormula()
    {
        Formula eigenvalues = Apply(new Formula.Subscript(Call("Matrix.IsHermitian.eigenvalues"), D(0)), Id("hR"));
        Formula rhs = Call("subentropySpectrum", Call("Fintype.card", Id("I")), eigenvalues);
        return Finite("I", All("R", MatrixType(Id("I")), All("hR", Call("Matrix.IsHermitian", Id("R")), Eqn(Call("subentropy", Id("R"), Id("hR")), rhs))));
    }
    private static Formula GuessFormula()
    {
        Formula positive = All("x", Id("X"), Call("Matrix.PosSemidef", Apply(Id("E"), Id("x"))));
        Formula identity = Eqn(SumOver("x", Id("X"), Apply(Id("E"), Id("x"))), D(1));
        Formula score = Call("Complex.re", SumOver("x", Id("X"), Call("Matrix.trace", Mul(Apply(Id("E"), Id("x")), Apply(Id("A"), Id("x"))))));
        Formula exists = ExistsAt("E", Arrow(Id("X"), MatrixType(Id("B"))), And(positive, And(identity, Eqn(Id("s"), score))));
        Formula rhs = Call("sSup", SetOf("s", Real, exists));
        return All("X", Call("Type"), All("B", Call("Type"),
            Seq(Bracket(Call("Fintype", Id("X"))), Bracket(Call("Fintype", Id("B"))), Bracket(Call("DecidableEq", Id("B"))),
                All("A", Arrow(Id("X"), MatrixType(Id("B"))), Eqn(Call("pGuess", Id("A")), rhs)))));
    }
    private static Formula ClaimBody()
    {
        Formula joint = Call("Matrix.blockDiagonal", Id("A"));
        Formula marginal = SumOver("x", Id("X"), Apply(Id("A"), Id("x")));
        Formula positive = All("x", Id("X"), Call("Matrix.PosSemidef", Apply(Id("A"), Id("x"))));
        Formula traceOne = Eqn(SumOver("x", Id("X"), Call("Matrix.trace", Apply(Id("A"), Id("x")))), D(1));
        Formula bound = Leq(Sub(Call("subentropy", joint, Id("hXB")), Call("subentropy", marginal, Id("hB"))), Seq(Minus, Call("Real.log", Call("pGuess", Id("A")))));
        Formula hermitian = All("hXB", Call("Matrix.IsHermitian", joint), All("hB", Call("Matrix.IsHermitian", marginal), bound));
        return EnsembleTypes(All("A", Arrow(Id("X"), MatrixType(Id("B"))), Imp(positive, Imp(traceOne, hermitian))));
    }
    private static Formula EnsembleTypes(Formula body) => All("X", Call("Type"), All("B", Call("Type"),
        Seq(Bracket(Call("Fintype", Id("X"))), Bracket(Call("DecidableEq", Id("X"))),
            Bracket(Call("Fintype", Id("B"))), Bracket(Call("DecidableEq", Id("B"))), body)));
    private static Formula Finite(string name, Formula body) => All(name, Call("Type"),
        Seq(Bracket(Call("Fintype", Id(name))), Bracket(Call("DecidableEq", Id(name))), body));
    private static Formula Natural => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula ENNRealType => Call("ENNReal");
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula MatrixType(Formula index) => Call("Matrix", index, index, Complex);
    private static Formula Id(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Bracket(Formula body) => Seq(OpenBracket, body, CloseBracket, Sp);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] args)
    {
        Formula[] words = name.Split('.').Select(part => (Formula)Seq(Operatorname, Grp(Id(part)))).ToArray();
        Formula symbol = Seq(words.SelectMany((part, index) => index == 0 ? new[] {part} : new[] {Dot, part}).ToArray());
        return args.Length == 0 ? symbol : Apply(symbol, args);
    }
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsAt(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula SumOver(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), InMacro, Sp, domain)), Parenthesized(body));
    private static Formula IntegralOver(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Int, Seq(Id(name), InMacro, Sp, domain)), Parenthesized(body), Sp, Id("d" + name));
    private static Formula SetOf(string name, Formula domain, Formula body) => Seq(OpenBrace, Id(name), Colon, Sp, domain, Sp, Bar, Sp, body, CloseBrace);
}
