using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class DissipatorSpectralDiskRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/chruscinskidenisovtarnowskizyczkowski2025spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A traceless diagonal jump on three complex coordinates gives an eigenvalue outside the disk determined by the pure-state scale.",
        H("The pure-state scale does not confine dissipative spectra"),
        Blocks(
            Definition("dissipator", "The dissipator of one jump", DissipatorFormula(),
                "For a complex square matrix L, the dissipator sends ρ to LρLᴴ minus one half "
                    + "of the sum LᴴLρ + ρLᴴL. Here Lᴴ is the conjugate transpose. "
                    + "This is one summand of the GKLS expression in bounding_6.tex, lines 205–209. "
                    + "There is no Hamiltonian commutator. The definition permits every natural N "
                    + "and every pair of matrices L and ρ, without a positivity or trace assumption."),
            Definition("generator", "A finite sum of dissipators", GeneratorFormula(),
                "The generator is the sum of the dissipators of L(k), weighted by the real rates γ(k). "
                    + "Each rate is explicitly included in the complex scalars by Complex.ofReal. "
                    + "A dot between a complex scalar and a matrix denotes scalar multiplication; "
                    + "between two matrices it denotes matrix multiplication. "
                    + "The expression is the purely dissipative part of the source's GKLS formula, "
                    + "bounding_6.tex, lines 205–209 and 227; line 702 fixes the purely dissipative scope. "
                    + "The definition itself allows arbitrary real rates, with nonnegativity imposed in claim."),
            Definition("scale", "The supremum over unit vectors", ScaleFormula(),
                "For every vector ψ with sum of squared coordinate norms equal to one, form the "
                    + "rank-one matrix ψψᴴ, apply the generator, and evaluate its quadratic form at ψ. "
                    + "The scale is the real supremum of the norms of these complex values. "
                    + "The star on a vector conjugates each coordinate; Matrix.vecMulVec forms the "
                    + "outer product, Matrix.mulVec is matrix-vector multiplication, and dotProduct "
                    + "is the bilinear dot product, so its first argument is explicitly conjugated. "
                    + "This is the supremum form of the pure-state maximum in Conjecture 3, "
                    + "bounding_6.tex, lines 1044–1049. No maximizing vector or positive scale "
                    + "is assumed in this definition."),
            Definition("claim", "The proposed disk bound", ClaimFormula(),
                "For every natural N and m, every family of nonnegative real rates and traceless "
                    + "complex jump matrices with strictly positive scale would satisfy the stated "
                    + "bound for every complex eigenvalue lam and nonzero eigenmatrix X. "
                    + "The bound says that lam divided by the scale lies in the closed disk of "
                    + "radius one centred at minus one. Complex.ofReal explicitly includes the real "
                    + "scale in the complex denominator. This is the spectral assertion of Conjecture 3, "
                    + "bounding_6.tex, lines 1044–1050, for finite purely dissipative GKLS sums. "
                    + "The traceless condition appears in the canonical form at lines 794–799. "
                    + "No orthogonality or normalization of the jump matrices is assumed here; "
                    + "zero rates are allowed and contribute zero summands."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A three-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take N = 3 and m = 1, put γ(k) = 1, and let L(k) be the diagonal matrix "
                            + "V = diag(1 − i/3, −1 − i/3, 2i/3). Its trace is zero: "
                            + "the two real parts cancel and the three imaginary parts sum to zero.")),
                    Paragraph(Text(
                        "For an arbitrary ψ in Fin 3 → ℂ, put p₀ = ‖ψ 0‖², p₁ = ‖ψ 1‖², "
                            + "and p₂ = ‖ψ 2‖². Expanding the diagonal products gives "
                            + "ψᴴ generator(γ,L,ψψᴴ) ψ = "
                            + "Complex.ofReal((p₀ − p₁)² + p₂² − (p₀ + p₁ + p₂)²). "
                            + "This identity holds before imposing normalization.")),
                    Paragraph(Text(
                        "If the squared coordinate norms of ψ sum to one, then p₀ + p₁ + p₂ = 1. "
                            + "All three p values are nonnegative. Set q = 1 − (p₀ − p₁)² − p₂². "
                            + "The identity q = 4p₀p₁ + 2p₂(p₀ + p₁) gives q ≥ 0, "
                            + "and the squared terms in its defining expression give q ≤ 1. "
                            + "The quadratic form is therefore Complex.ofReal(−q), whose norm is q ≤ 1. "
                            + "The set defining the scale is nonempty: ψ = (1,0,0) gives value zero. "
                            + "Taking its supremum proves scale(γ,L) ≤ 1.")),
                    Paragraph(Text(
                        "Next choose ψ = ((1+i)/2,(1+i)/2,0). Since ‖1+i‖² = 2, "
                            + "its squared coordinate norms sum to one and p₀ = p₁ = 1/2, p₂ = 0. "
                            + "The same quadratic-form identity gives norm one. "
                            + "The preceding bound makes the set of values bounded above, "
                            + "so membership of the value one implies 1 ≤ scale(γ,L), "
                            + "and in particular scale(γ,L) > 0.")),
                    Paragraph(Text(
                        "Let X be the matrix with entry one at row 0, column 1 and zero elsewhere. "
                            + "Expanding the nine entries gives generator(γ,L,X) = "
                            + "(−2 + (2/3)i)X. Thus lam = −2 + (2/3)i is an eigenvalue.")),
                    Paragraph(Text(
                        "For any real ν with 0 < ν ≤ 1, the squared norm of "
                            + "1 + (−2 + (2/3)i)/Complex.ofReal(ν) is "
                            + "(1 − 2/ν)² + (2/(3ν))². Its difference from one is "
                            + "(40/9 − 4ν)/ν² > 0. Nonnegativity of the norm then gives "
                            + "a norm strictly greater than one.")),
                    Paragraph(Text(
                        "Suppose claim held. Apply it to N = 3, m = 1 and the family above: "
                            + "the rate is nonnegative, every jump has trace zero, and the scale is positive. "
                            + "The matrix X is nonzero because its (0,1) entry is one. "
                            + "Its eigenvalue equation would give a disk norm at most one. "
                            + "Applying the strict inequality with ν = scale(γ,L), using its positivity "
                            + "and upper bound by one, contradicts that conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chruscinski-denisov-tarnowski-zyczkowski-2025-dissipator-spectral-disk-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DissipatorFormula() => All(N, Naturals, All(L, MatrixN, All(Rho, MatrixN,
        Equal(Local("dissipator", L, Rho),
            Subtract(Multiply(Multiply(L, Rho), Adjoint(L)),
                Multiply(Typed(Div(D(1), D(2)), Complexes),
                    Parenthesized(Add(Multiply(Multiply(Adjoint(L), L), Rho),
                        Multiply(Rho, Parenthesized(Multiply(Adjoint(L), L)))))))))));

    private static Formula GeneratorFormula() => Parameters(All(Rho, MatrixN,
        Equal(Local("generator", GammaLower, L, Rho),
            SumOver(F.Id("k"), Fin(M), Multiply(OfReal(App(GammaLower, F.Id("k"))),
                Local("dissipator", App(L, F.Id("k")), Rho))))));

    private static Formula ScaleFormula()
    {
        var values = Seq(OpenBrace, F.Id("r"), Colon, Sp, Reals, Sp, Mid, Sp,
            Some(Psi, VectorN, And(
                Equal(SumOver(F.Id("i"), Fin(N), SquaredNorm(App(Psi, F.Id("i")))),
                    Typed(D(1), Reals)),
                Equal(F.Id("r"), new Formula.Norm(QuadraticForm())))), CloseBrace);
        return Parameters(Equal(Local("scale", GammaLower, L), Call("sSup", values)));
    }

    private static Formula ClaimFormula()
    {
        var rateCondition = All(F.Id("k"), Fin(M),
            LE(Typed(D(0), Reals), App(GammaLower, F.Id("k"))));
        var traceCondition = All(F.Id("k"), Fin(M),
            Equal(App(Qualified("Matrix", "trace"), App(L, F.Id("k"))), Typed(D(0), Complexes)));
        var eigenvalueCondition = Equal(Local("generator", GammaLower, L, F.Id("X")),
            Multiply(F.Id("lam"), F.Id("X")));
        var diskBound = LE(new Formula.Norm(Add(Typed(D(1), Complexes),
            Div(F.Id("lam"), OfReal(Local("scale", GammaLower, L))))), Typed(D(1), Reals));
        return Equal(Named("claim"), Parenthesized(Parameters(
            Imp(rateCondition, Imp(traceCondition,
                Imp(LT(Typed(D(0), Reals), Local("scale", GammaLower, L)),
                    All(F.Id("lam"), Complexes, All(F.Id("X"), MatrixN,
                        Imp(NotEqual(F.Id("X"), Typed(D(0), MatrixN)),
                            Imp(eigenvalueCondition, diskBound))))))))));
    }

    private static Formula QuadraticForm() => Call("dotProduct", Call("star", Psi),
        App(Qualified("Matrix", "mulVec"),
            Local("generator", GammaLower, L,
                App(Qualified("Matrix", "vecMulVec"), Psi, Call("star", Psi))), Psi));

    private static Formula Parameters(Formula body) => All(N, Naturals, All(M, Naturals,
        All(GammaLower, Arrow(Fin(M), Reals), All(L, Arrow(Fin(M), MatrixN), body))));

    private static Formula N => F.Id("N");
    private static Formula M => F.Id("m");
    private static Formula L => F.Id("L");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula MatrixN => Call("Matrix", Fin(N), Fin(N), Complexes);
    private static Formula VectorN => Arrow(Fin(N), Complexes);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string first, string second) =>
        Seq(Operatorname, Grp(F.Id(first), Dot, F.Id(second)));
    private static Formula Local(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula OfReal(Formula value) => App(Qualified("Complex", "ofReal"), value);
    private static Formula Adjoint(Formula value) => App(Qualified("Matrix", "conjTranspose"), value);
    private static Formula SquaredNorm(Formula value) => new Formula.Power(new Formula.Norm(value), D(2));
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula And(Formula first, Formula second) =>
        new Formula.Logic(Parenthesized(first), FormulaLogicOperator.And, Parenthesized(second));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
