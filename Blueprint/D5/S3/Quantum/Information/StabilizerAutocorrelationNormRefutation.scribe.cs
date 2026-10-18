using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class StabilizerAutocorrelationNormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/stacey2025sicsmajorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In dimension five, a Fourier Clifford changes the Euclidean operator norm of the matrix of cyclic MUB probability autocorrelations.",
        H("Clifford transformations can change the autocorrelation operator norm"),
        Blocks(
            Paragraph(Text(
                "All indices in Fin(5) are residues modulo five, represented by 0, 1, 2, 3 and 4; "
                    + "val takes the corresponding natural-number representative. "
                    + "The six basis labels are Option(Fin(5)): ∞ denotes none, and some(m) is the finite label m. "
                    + "Write ω, τ, X, Z, D, P, p, A, F and ψ for omega, tau, shift, clock, displacement, "
                    + "projector, probability, autocorr, fourier and psi, respectively. "
                    + "I is the imaginary unit; a star on a matrix denotes conjugate transpose. "
                    + "Matrix norms with subscript op are induced by the Euclidean norms on both index spaces.")),
            Node("omega", "The fifth root of unity", OmegaFormula(),
                "The standard positive fifth root is exp(2πI/5). This is the Weyl–Heisenberg root used in Section I.",
                AssessedProvenance.FromLiterature(Source)),
            Node("tau", "The displacement phase", Equal(Tau, Power(Omega, D(3))),
                "In dimension five, the standard phase −exp(πI/5) equals ω cubed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("shift", "The cyclic shift", ShiftFormula(),
                "The shift sends the computational vector at j to the vector at j + 1. Addition is in Fin(5).",
                AssessedProvenance.FromLiterature(Source)),
            Node("clock", "The clock matrix", ClockFormula(),
                "The clock is diagonal, with entry ω to the power val(j) at j. Together X and Z are the standard Weyl generators.",
                AssessedProvenance.FromLiterature(Source)),
            Node("displacement", "Weyl–Heisenberg displacements", DisplacementFormula(),
                "The phase exponent uses the product of the natural representatives of p and q. "
                    + "Scalar multiplication is denoted by a centered dot; the two matrix powers are multiplied in the order X then Z.",
                AssessedProvenance.FromLiterature(Source)),
            Node("projector", "The six MUB projector families", ProjectorFormula(),
                "These are the standard spectral projectors of the Weyl lines. "
                    + "The infinite line uses D(r,0), and the finite line m uses D(mr,r). "
                    + "The product −jr is taken modulo five before val supplies the exponent; "
                    + "the finite-line product mr is also in Fin(5). Each sum runs over all five residues.",
                AssessedProvenance.FromLiterature(Source)),
            Node("probability", "Born probabilities", ProbabilityFormula(),
                "Section III uses the probability of outcome j in basis m. "
                    + "Here it is the real part of the expectation of P(m,j). "
                    + "The star on a vector conjugates each coordinate, and dotProduct is the bilinear sum of coordinate products. "
                    + "The definition is given for every complex vector; normalization is imposed in claim.",
                AssessedProvenance.FromLiterature(Source)),
            Node("autocorr", "The rectangular autocorrelation matrix", AutocorrelationFormula(),
                "Section III defines A by the cyclic autocorrelation of each MUB probability vector. "
                    + "It is a real matrix with six rows and five columns. The outcome j + k is computed modulo five.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsClifford", "The Clifford condition", CliffordFormula(),
                "The matrix is unitary on both sides and conjugates each Weyl generator to a displacement times a unit-modulus phase. "
                    + "The displacement labels and phase may differ for X and Z. "
                    + "This is the standard normalizer condition on the two generators.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Clifford invariance of the Euclidean operator norm", ClaimFormula(),
                "Section III asserts that Clifford action permutes the rows and columns of A and hence preserves every unitarily invariant norm. "
                    + "The proposition here is its Euclidean operator-norm consequence in dimension five. "
                    + "It quantifies over every vector whose squared complex moduli sum to one and every matrix satisfying IsClifford. "
                    + "The function normSq is the squared complex modulus.",
                AssessedProvenance.FromLiterature(Source)),
            Node("fourier", "The Fourier matrix", FourierFormula(),
                "Choose the positive-exponent Fourier matrix. Its row and column labels multiply modulo five before val is taken; "
                    + "the denominator is the positive real square root, regarded as a complex number.",
                AssessedProvenance.FromRepo(Source)),
            Node("psi", "A two-coordinate unit vector", StateFormula(),
                "Choose ψ = (1,1,0,0,0)/√2 in computational order. Its squared moduli sum to one.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("stacey-autocorr-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The operator norm changes under a Fourier Clifford"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let W have entries stdAddChar(ji) for residues i,j modulo five. "
                            + "The identity WW* = 5I and F = W/√5 give F*F = FF* = 1. "
                            + "The entry relations FX = ZF and FZ = D(4,0)F then give FXF* = D(0,1) = Z, "
                            + "and FZF* = D(4,0) = X to the fourth power. "
                            + "Both phases are one, so F satisfies IsClifford. "
                            + "Its action on the chosen unit vector has coordinate (1 + ω to the power val(i))/√10 at i.")),
                    Paragraph(Text(
                        "For the exact probability tables, put a = (3 − √5)/20 and b = (3 + √5)/20, "
                            + "and list outcomes in the order 0,1,2,3,4. "
                            + "For ψ, the rows at ∞,0,1,2,3,4 are respectively "
                            + "(2/5,b,a,a,b), (1/2,1/2,0,0,0), (a,a,b,2/5,b), "
                            + "(b,b,a,2/5,a), (b,b,a,2/5,a), (a,a,b,2/5,b). "
                            + "For Fψ, the rows in the same order are "
                            + "(1/2,0,0,0,1/2), (2/5,b,a,a,b), (a,b,2/5,b,a), "
                            + "(b,a,a,b,2/5), (b,2/5,b,a,a), (a,a,b,2/5,b). "
                            + "These values follow by expanding the displacement entries and the fifth roots of unity.")),
                    Paragraph(Text(
                        "Taking cyclic autocorrelations gives the rows R = (1/2,1/4,0,0,1/4), "
                            + "S = (3/10,(7 + √5)/40,(7 − √5)/40,(7 − √5)/40,(7 + √5)/40), "
                            + "and T = (3/10,(7 − √5)/40,(7 + √5)/40,(7 + √5)/40,(7 − √5)/40). "
                            + "The rows of A(ψ) are S,R,S,T,T,S, while those of A(Fψ) are R,S,S,S,S,S.")),
                    Paragraph(Text(
                        "The squared Frobenius norm of A(ψ)*A(ψ) is (2961 + 19√5)/1600. "
                            + "The operator norm is bounded by the Frobenius norm, so the fourth power of the operator norm of A(ψ) "
                            + "is at most this value and its square is less than 7/5. "
                            + "Use S as a test vector for A(Fψ). Its squared Euclidean norm is 9/40, "
                            + "and its image has squared norm (993 + 19√5)/3200. "
                            + "Thus the squared operator norm of A(Fψ) is at least (993 + 19√5)/720, which exceeds 7/5. "
                            + "The two operator norms differ. Applying claim to ψ and F would equate them, proving its negation. "
                            + "In particular, the change of cyclic-difference labels cannot always be expressed by a single common column permutation."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("stacey-2025-autocorrelation-norm-clifford-invariance-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("stacey-autocorr-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => Apply(Named(name), arguments);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Both(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Either(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula ImpliesTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Product(Formula left, Formula right) =>
        Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula Scale(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Adj(Formula value) => Power(value, Star);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Root(byte value) => Seq(Sqrt, Grp(D(value)));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, Parenthesized(yes),
        Sp, Named("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(Formula variable, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Colon, Sp, FinFive()), Sp, Parenthesized(body));
    private static Formula FinFive() => Call("Fin", D(5));
    private static Formula Labels() => Call("Option", FinFive());
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vectors() => Parenthesized(new Formula.TypeArrow(FinFive(), Complexes()));
    private static Formula Matrices() => Call("Matrix", FinFive(), FinFive(), Complexes());
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Displace(Formula p, Formula q) => Call("D", p, q);
    private static Formula Project(Formula m, Formula j) => Call("P", m, j);
    private static Formula Prob(Formula vector, Formula m, Formula j) => Call("p", vector, m, j);
    private static Formula Correlation(Formula vector) => Call("A", vector);
    private static Formula OpNorm(Formula value) => new Formula.Subscript(new Formula.Norm(value), Named("op"));

    private static Formula OmegaFormula() => Equal(Omega,
        Call("exp", Fraction(Product(Product(D(2), Pi), Named("I")), D(5))));

    private static Formula ShiftFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Equal(F.Id("X"), LambdaOf(i, FinFive(), LambdaOf(j, FinFive(),
            If(Equal(i, Add(j, D(1))), D(1), D(0)))));
    }

    private static Formula ClockFormula()
    {
        Formula j = F.Id("j");
        return Equal(F.Id("Z"), Call("diagonal", LambdaOf(j, FinFive(), Power(Omega, Val(j)))));
    }

    private static Formula DisplacementFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        return All(p, FinFive(), All(q, FinFive(), Equal(Displace(p, q),
            Scale(Power(Tau, Product(Val(p), Val(q))),
                Product(Power(F.Id("X"), Val(p)), Power(F.Id("Z"), Val(q)))))));
    }

    private static Formula ProjectorFormula()
    {
        Formula m = F.Id("m"), j = F.Id("j"), r = F.Id("r");
        Formula phase = Power(Omega, Val(Product(new Formula.Negate(j), r)));
        Formula infinite = Scale(Fraction(D(1), D(5)), SumOver(r, Scale(phase, Displace(r, D(0)))));
        Formula finite = Scale(Fraction(D(1), D(5)), SumOver(r, Scale(phase, Displace(Product(m, r), r))));
        return Both(All(j, FinFive(), Equal(Project(Infty, j), infinite)),
            All(m, FinFive(), All(j, FinFive(), Equal(Project(Call("some", m), j), finite))));
    }

    private static Formula ProbabilityFormula()
    {
        Formula v = F.Id("v"), m = F.Id("m"), j = F.Id("j");
        Formula expectation = Call("dotProduct", Call("star", v), Call("mulVec", Project(m, j), v));
        return All(v, Vectors(), All(m, Labels(), All(j, FinFive(),
            Equal(Prob(v, m, j), Apply(Re, expectation)))));
    }

    private static Formula AutocorrelationFormula()
    {
        Formula v = F.Id("v"), m = F.Id("m"), k = F.Id("k"), j = F.Id("j");
        return All(v, Vectors(), Equal(Correlation(v), LambdaOf(m, Labels(), LambdaOf(k, FinFive(),
            SumOver(j, Product(Prob(v, m, j), Prob(v, m, Add(j, k))))))));
    }

    private static Formula GeneratorCondition(Formula u, Formula generator)
    {
        Formula p = F.Id("p"), q = F.Id("q"), z = F.Id("z");
        return Some(p, FinFive(), Some(q, FinFive(), Some(z, Complexes(),
            Both(Equal(new Formula.Norm(z), D(1)),
                Equal(Product(Product(u, generator), Adj(u)), Scale(z, Displace(p, q)))))));
    }

    private static Formula CliffordFormula()
    {
        Formula u = F.Id("U");
        Formula body = Both(Equal(Product(Adj(u), u), D(1)),
            Both(Equal(Product(u, Adj(u)), D(1)),
                Both(GeneratorCondition(u, F.Id("X")), GeneratorCondition(u, F.Id("Z")))));
        return All(u, Matrices(), IffTo(Call("IsClifford", u), body));
    }

    private static Formula ClaimFormula()
    {
        Formula v = F.Id("v"), i = F.Id("i"), u = F.Id("U");
        Formula normalized = Equal(SumOver(i, Call("normSq", Apply(v, i))), D(1));
        Formula invariant = Equal(OpNorm(Correlation(Call("mulVec", u, v))), OpNorm(Correlation(v)));
        return IffTo(Named("claim"), All(v, Vectors(), ImpliesTo(normalized,
            All(u, Matrices(), ImpliesTo(Call("IsClifford", u), invariant)))));
    }

    private static Formula FourierFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Equal(F.Id("F"), LambdaOf(i, FinFive(), LambdaOf(j, FinFive(),
            Fraction(Power(Omega, Val(Product(i, j))), Typed(Root(5), Complexes())))));
    }

    private static Formula StateFormula()
    {
        Formula j = F.Id("j");
        return Equal(Psi, LambdaOf(j, FinFive(), If(Either(Equal(j, D(0)), Equal(j, D(1))),
            Power(Typed(Root(2), Complexes()), new Formula.Negate(D(1))), D(0))));
    }
}
