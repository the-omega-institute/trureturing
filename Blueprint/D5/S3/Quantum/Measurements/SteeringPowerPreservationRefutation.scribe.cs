using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class SteeringPowerPreservationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/ortheyaugusiak2025steering");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible five-dimensional projective family fails steering power preservation.",
        H("The steering substitution need not preserve powers"),
        Blocks(
            Paragraph(Text(
                "Fin d consists of the natural numbers below d, and Fin.val gives the natural representative. "
                    + "The function windowRoot d is exp(2πi/d), with the real and natural quantities included in the complex numbers. "
                    + "Complex.I is the imaginary unit, Complex.ofReal is the inclusion of the reals, and Nat.cast includes a natural number in the indicated scalar field. "
                    + "A star on a complex number means complex conjugation. Matrix multiplication and powers use the usual complex matrix algebra; a centered dot denotes scalar multiplication. "
                    + "Nat.div and Nat.mod are natural-number division and remainder, and subtraction between natural numbers is truncated at zero.")),
            Node("coeff", "steering-coeff", "The phase coefficients", CoeffFormula(),
                "For real phases φ, coeff d φ n y k is the coefficient of the nth-power steering substitution. "
                    + "The inner sum uses m = 0, …, n − 1, so the phase index is l + m + 1 modulo d. "
                    + "The bound on l implies d > 0 whenever such an index is needed. "
                    + "Angle brackets designate the element of Fin d with the displayed natural representative. "
                    + "The real phase sum is included in ℂ before multiplication by −Complex.I. "
                    + "This is the coefficient in main2.tex, lines 204–206; the definition also allows every natural n and d.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Admissible", "steering-admissible", "Admissible phases", AdmissibleFormula(),
                "Each column of phases has real sum zero. For each natural n from 1 through d − 1, the coefficient rows indexed by y are orthonormal: "
                    + "the conjugated row is indexed by y′ and the unconjugated row by y. "
                    + "These are the zero-phase condition of main2.tex, lines 190–194 and 208–212, and the orthogonality condition of lines 234–236. "
                    + "At d = 0 or d = 1 there is no n in the specified interval.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsProjectiveFamily", "steering-projective-family", "Projective observables", ProjectiveFormula(),
                "For each y, the complex d by d matrix B y is unitary and its dth power is the identity matrix. "
                    + "Thus its order divides d. This is the projective-observable condition of main2.tex, line 355, restricted to the Hilbert space ℂᵈ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("transformed", "steering-transformed", "The steering substitution", TransformedFormula(),
                "The nth transformed operator at k is the sum of the nth powers of B y weighted by coeff d φ n y k. "
                    + "For projective observables these powers are the Fourier components indexed by n and y of the measurement. "
                    + "The definition is the substitution rule of main2.tex, lines 246–249, in the projective setting of line 355. "
                    + "It is defined for arbitrary B and phases, without assuming projectivity or admissibility.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "steering-claim", "Universal preservation of powers", ClaimFormula(),
                "For every prime natural d, every admissible phase array and every projective family on ℂᵈ, "
                    + "the transformed operator at every k and every power n from 1 through d − 1 equals the nth power of the first transformed operator. "
                    + "This is the dimension-d matrix reading of Conjecture 1 in main2.tex, lines 1265–1273, under the projective assumption at line 1263. "
                    + "The conjecture permits Bob a larger Hilbert space; the displayed proposition only quantifies over d by d matrices. "
                    + "There is no hypothesis about a shared state or a measured violation of a steering inequality.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("steering-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A five-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 5 and write ω = windowRoot 5. The primitive fifth root satisfies ω⁵ = 1, "
                            + "1 + ω + ω² + ω³ + ω⁴ = 0 and star(ω) = ω⁴. "
                            + "For each y in Fin 5 choose the integer vector (−6(y.val : ℤ), 0, (y.val : ℤ) − 1, 1 + 2(y.val : ℤ), 3(y.val : ℤ)), "
                            + "include its coordinates in ℝ, and multiply them by 2π/5 to obtain φ(·,y). "
                            + "The five coordinates sum to zero. For every integer a, the exponential of −i(2π/5)(a : ℝ) is ω raised to the natural representative of (−a) modulo 5. "
                            + "Consequently all coefficient terms reduce to powers of ω with natural exponents modulo 5. "
                            + "For n = 1, 2, 3, 4 and all y,y′, expand the five-term sums, replace star(ω) by ω⁴, reduce exponents modulo 5 and replace ω⁴ by −1 − ω − ω² − ω³. "
                            + "The resulting polynomial identities give the required coefficient orthogonality, so these phases are admissible.")),
                    Paragraph(Text(
                        "Use D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.shift and "
                            + "D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.clock. "
                            + "The matrix shift sends the coordinate vector at j to the vector at j + 1 modulo five; clock is diagonal with entry ω to the natural power j.val. "
                            + "For each y define Rᵧ as the sum over k in Fin 5 of star(coeff 5 φ 1 y k) times the matrix product of shift with clock^(k.val). "
                            + "The entries of shift are one exactly when the row i is j + 1, and zero otherwise. "
                            + "Expanding the coefficients in Rᵧ gives its (i,j) entry as zero unless i = j + 1; at that row it is ω^((aⱼ + y.val · j.val) mod 5), with a = (0,4,1,0,0).")),
                    Paragraph(Text(
                        "Let U be the diagonal matrix with entries ω raised to the corresponding coordinates of (0,0,4,0,0). "
                            + "Each diagonal entry has modulus one, so U is unitary. The entry formula gives Rᵧ = U (shift clock^(y.val)) U*, using matrix multiplication and conjugate transpose. "
                            + "Both shift and clock are unitary, hence so is this product. "
                            + "To compute its fifth power, identify Fin 5 with ZMod 5 and apply the Weyl displacement power identity to the displacement with labels 1 and y. "
                            + "The natural numbers 5 and choose(5,2) = 10 both cast to zero in ZMod 5; the identity therefore gives fifth power one. "
                            + "Reindexing the matrices back to Fin 5 gives (shift clock^(y.val))⁵ = 1. "
                            + "Conjugation by U preserves powers, so Rᵧ⁵ = 1. "
                            + "Now take B₀ = ω R₀ and Bᵧ = Rᵧ for y ≠ 0. Multiplication by the scalar ω preserves unitarity and the fifth power, so B is a projective family.")),
                    Paragraph(Text(
                        "At k = 0, expanding the same finite sums and matrix entries gives two reconstructions: "
                            + "the sum of coeff 5 φ 1 y 0 times Rᵧ is shift, and the sum of coeff 5 φ 2 y 0 times Rᵧ² is shift². "
                            + "Set g = (3 + ω + ω⁴)/5. Direct evaluation gives coeff 5 φ 1 0 0 = g and coeff 5 φ 2 0 0 = g. "
                            + "Only B₀ differs from R₀. Thus transformed 5 φ B 1 0 = shift + ((ω − 1)g) R₀, "
                            + "and transformed 5 φ B 2 0 = shift² + ((ω² − 1)g) R₀², where the products of complex coefficients with matrices are scalar multiplications. "
                            + "Expanding the square of the first matrix and using the entry formula for R₀ gives the (0,3) entry of "
                            + "(transformed 5 φ B 1 0)² − transformed 5 φ B 2 0 as g(g − 1)(ω − 1)².")),
                    Paragraph(Text(
                        "Put s = ω + ω⁴. The fifth-root identities give s² + s = 1. If g = 0, then s = −3 and this equation reads 6 = 1; "
                            + "if g = 1, then s = 2 and it again reads 6 = 1. Hence g is neither zero nor one. "
                            + "Primitivity gives ω ≠ 1, so g(g − 1)(ω − 1)² is nonzero. "
                            + "If claim held, apply it to the prime 5, the admissible phases φ and the projective family B with k = 0 and n = 2. "
                            + "Since 1 ≤ 2 ≤ 4, it would identify transformed 5 φ B 2 0 with (transformed 5 φ B 1 0)², forcing this same (0,3) entry to vanish. "
                            + "This contradiction proves the negation of claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("orthey-augusiak-2025-steering-power-preservation-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string id, string title, Formula formula,
        string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CoeffFormula()
    {
        Formula index = Typed(Seq(Langle, Sp,
            At(Name("Nat", "mod"), Add(Add(Val("l"), X("m")), D(1)), X("d")),
            Sp, Rangle), FinD());
        Formula phases = SumIn("m", Naturals(), At(Name("Finset", "range"), X("n")),
            At(Phi, index, X("y")));
        Formula complexPhases = Typed(At(Name("Complex", "ofReal"), Typed(phases, Reals())), Complexes());
        Formula exponential = At(Name("Complex", "exp"),
            Mul(new Formula.Negate(Name("Complex", "I")), complexPhases));
        Formula firstExponent = At(Name("Nat", "div"),
            Mul(Mul(Val("k"), X("n")), Sub(X("n"), D(1))), D(2));
        Formula summand = Mul(exponential, Pow(Root(), Mul(Mul(Val("k"), X("n")), Val("l"))));
        Formula body = Mul(Mul(new Formula.Fraction(Typed(D(1), Complexes()),
                Typed(At(Name("Nat", "cast"), X("d")), Complexes())), Pow(Root(), firstExponent)),
            SumOver("l", FinD(), summand));
        return PhaseBinders(All("n", Naturals(), All("y", FinD(), All("k", FinD(),
            Eqn(Typed(Call("coeff", X("d"), Phi, X("n"), X("y"), X("k")), Complexes()), body)))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula zeroPhases = All("y", FinD(),
            Eqn(SumOver("j", FinD(), At(Phi, X("j"), X("y"))), Typed(D(0), Reals())));
        Formula orthogonality = All("y", FinD(), All("y'", FinD(),
            Eqn(SumOver("k", FinD(),
                    Mul(Call("star", Call("coeff", X("d"), Phi, X("n"), X("y'"), X("k"))),
                        Call("coeff", X("d"), Phi, X("n"), X("y"), X("k")))),
                Call("ite", Eqn(X("y"), X("y'")), Typed(D(1), Complexes()), Typed(D(0), Complexes())))));
        return PhaseBinders(IffOf(Call("Admissible", X("d"), Phi),
            AndOf(zeroPhases, All("n", Naturals(),
                ImpliesOf(LE(D(1), X("n")), ImpliesOf(LE(X("n"), Sub(X("d"), D(1))), orthogonality))))));
    }

    private static Formula ProjectiveFormula() => All("d", Naturals(), All("B", Family(),
        IffOf(Call("IsProjectiveFamily", X("d"), X("B")), All("y", FinD(), AndOf(
            new Formula.Relation(At(X("B"), X("y")), FormulaRelationOperator.MemberOf,
                At(Name("Matrix", "unitaryGroup"), FinD(), Complexes())),
            Eqn(Pow(At(X("B"), X("y")), X("d")), Typed(D(1), MatrixType())))))));

    private static Formula TransformedFormula() => PhaseBinders(All("B", Family(),
        All("n", Naturals(), All("k", FinD(), Eqn(
            Typed(Call("transformed", X("d"), Phi, X("B"), X("n"), X("k")), MatrixType()),
            SumOver("y", FinD(), Smul(Call("coeff", X("d"), Phi, X("n"), X("y"), X("k")),
                Pow(At(X("B"), X("y")), X("n")))))))));

    private static Formula ClaimFormula()
    {
        Formula equality = Eqn(Call("transformed", X("d"), Phi, X("B"), X("n"), X("k")),
            Pow(Call("transformed", X("d"), Phi, X("B"), D(1), X("k")), X("n")));
        return IffOf(Local("claim"), All("d", Naturals(),
            ImpliesOf(At(Name("Nat", "Prime"), X("d")), All("φ", PhaseType(),
                ImpliesOf(Call("Admissible", X("d"), Phi), All("B", Family(),
                    ImpliesOf(Call("IsProjectiveFamily", X("d"), X("B")),
                        All("k", FinD(), All("n", Naturals(),
                            ImpliesOf(LE(D(1), X("n")),
                                ImpliesOf(LE(X("n"), Sub(X("d"), D(1))), equality)))))))))));
    }

    private static Formula X(string name) => name switch
    {
        "φ" => Phi,
        "y'" => Seq(F.Id("y"), Apos),
        _ => F.Id(name),
    };
    private static Formula Name(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Name(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinD() => Call("Fin", X("d"));
    private static Formula MatrixType() => Call("Matrix", FinD(), FinD(), Complexes());
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula PhaseType() => Arrow(FinD(), Arrow(FinD(), Reals()));
    private static Formula Family() => Arrow(FinD(), MatrixType());
    private static Formula Val(string name) => Typed(At(Name("Fin", "val"), X(name)), Naturals());
    private static Formula Root() => Call("windowRoot", X("d"));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula PhaseBinders(Formula body) => All("d", Naturals(), All("φ", PhaseType(), body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Typed(X(name), type), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula AndOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
