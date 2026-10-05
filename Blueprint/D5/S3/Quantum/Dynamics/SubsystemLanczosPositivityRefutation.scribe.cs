using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class SubsystemLanczosPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/caputadigiuliolo2026complexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first squared subsystem Lanczos coefficient can be negative for an entangled two-qubit state.",
        H("Subsystem Lanczos positivity fails"),
        Blocks(
            Node("rho", "The evolved pure density", RhoFormula(),
                "Section 3.1, printed p. 17, writes: \"full density matrix ρ(t)=|ψ(t)⟩⟨ψ(t)| before the partial trace\". The initial pure density is rankOneDensity(ψ) = ψψᴴ, using the existing rank-one density definition. The source exponential exp(−i t H) equals hamiltonianPropagator(H,t): real scalar multiplication followed by the generator −iH gives the same exponent. Conjugation by this propagator gives the full evolved density. The symbols a and b are the finite subsystem dimensions; matrix products are ordinary matrix multiplication, and matrix norms use the L² operator norm.",
                "rho", DescribeRole.Definition),
            Node("rhoa", "The reduced density", RhoAFormula(),
                "Section 3.1, printed p. 14, says: \"we have a corresponding non-unitary evolution for the reduced density matrices ρ_A(t) and ρ_B(t).\" The operation partialTraceRight sums the B diagonal index of the full density and returns the matrix on Fin a.",
                "rhoA", DescribeRole.Definition),
            Node("return", "The subsystem return amplitude", ReturnFormula(),
                "Section 3.1, printed pp. 14-15, defines R_A(t) = Tr(ρ_A(t)ρ_A(0))/Tr(ρ_A(0)²). It says: \"For this reason, throughout the manuscript we refer to R_A(t) as the subsystem return amplitude.\" The real part selects the real carrier of these trace overlaps; the source explicitly notes R_A*(t) = R_A(t). The denominator is the initial reduced purity, without a time-dependent normalization. Equation labels generaldef_RL and subsystem moments identify the definitions; the v2 PDF numbers them (3.2) and (3.3).",
                "returnAmplitude", DescribeRole.Definition),
            Node("moment", "Moments at zero", MomentFormula(),
                "Section 3.1, printed p. 15, defines μ_n^(A) = ∂_t^n R_A(t)|_(t=0). The operation iteratedDeriv is Mathlib's n-fold real derivative, evaluated at 0. Equation (3.5) of the v2 PDF, labeled b1_generalprocedure in the TeX, gives (b₁^(A))² = (μ₁^(A))² − μ₂^(A).",
                "moment", DescribeRole.Definition),
            Node("claim", "The first clause of the conjecture", ClaimFormula(),
                "Section 3.1, printed p. 15 (PDF page 16), states: \"At present, however, we are unable to establish the sign of (bₙ⁽ᴬ⁾)² in full generality. Based on all the examples discussed in this manuscript, we conjecture that (bₙ⁽ᴬ⁾)²>0 for every n, and hence that all the coefficients bₙ⁽ᴬ⁾ are real.\" The predicate claim is its n = 1 clause over every finite pair of subsystem dimensions, every normalized pure initial state, and every Hermitian time-independent Hamiltonian. The norm is the Euclidean norm of ψ. A counterexample to this clause refutes the universal sign conjecture.",
                "claim", DescribeRole.Definition),
            Node("result", "Refutation by an entangled two-qubit state", Disp(new Formula.Not(F.Id("claim"))),
                "Section 3.1, printed p. 15, conjectures: \"At present, however, we are unable to establish the sign of (bₙ⁽ᴬ⁾)² in full generality. Based on all the examples discussed in this manuscript, we conjecture that (bₙ⁽ᴬ⁾)²>0 for every n, and hence that all the coefficients bₙ⁽ᴬ⁾ are real.\" Take ψ = (3/5)|00⟩ + (4/5)|11⟩ and H = X_A ⊗ |0⟩⟨0|_B. The state has norm one and H is Hermitian. Differentiating the matrix exponential, conjugation, partial trace and fixed-normalization overlap yields initial purity 337/625, first overlap derivative 0, and second overlap derivative 126/625. Thus moment(ψ,H,1) = 0 and moment(ψ,H,2) = 126/337. The witness has (μ_1)^2 − μ_2 = −126/337, so the first squared coefficient contradicts strict positivity. No higher Lanczos coefficient is needed for the refutation.",
                "result", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("caputa-di-giulio-loc-subsystem-lanczos-positivity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, bool derived = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("subsystem-lanczos-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Num(int n) => new Formula.Number(n);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index(Formula a, Formula b) => Call("Prod", Call("Fin", a), Call("Fin", b));
    private static Formula MatrixType(Formula a, Formula b)
    {
        Formula index = Index(a, b);
        return Call("Matrix", index, index, Complex());
    }
    private static Formula StateSpace(Formula a, Formula b) => Call("EuclideanSpace", Complex(), Index(a, b));
    private static Formula Dims(Formula body) => All("a", Nat(), All("b", Nat(), body));
    private static Formula Data(Formula body) => Dims(All("psi", StateSpace(F.Id("a"), F.Id("b")),
        All("H", MatrixType(F.Id("a"), F.Id("b")), body)));
    private static Formula Time(Formula body) => Data(All("t", Real(), body));

    private static Formula RhoFormula()
    {
        Formula psi = F.Id("psi"), h = F.Id("H"), t = F.Id("t"), u = Call("hamiltonianPropagator", h, t);
        Formula source = Call("exp", Mul(Mul(new Formula.Negate(F.Id("i")), t), h));
        return Disp(Time(new Formula.Logic(Eqn(u, source), FormulaLogicOperator.And,
            Eqn(Call("rho", psi, h, t),
                Mul(Mul(u, Call("rankOneDensity", psi)), Call("conjTranspose", u))))));
    }

    private static Formula RhoAFormula() => Disp(Time(Eqn(Call("rhoA", F.Id("psi"), F.Id("H"), F.Id("t")),
        Call("partialTraceRight", Call("rho", F.Id("psi"), F.Id("H"), F.Id("t"))))));

    private static Formula ReturnFormula()
    {
        Formula psi = F.Id("psi"), h = F.Id("H"), t = F.Id("t");
        Formula initial = Call("rhoA", psi, h, Num(0));
        Formula numerator = Call("re", Call("trace", Mul(Call("rhoA", psi, h, t), initial)));
        Formula denominator = Call("re", Call("trace", Mul(initial, initial)));
        return Disp(Time(Eqn(Call("returnAmplitude", psi, h, t), new Formula.Fraction(numerator, denominator))));
    }

    private static Formula MomentFormula() => Disp(Data(All("n", Nat(),
        Eqn(Call("moment", F.Id("psi"), F.Id("H"), F.Id("n")),
            Call("iteratedDeriv", F.Id("n"), Call("returnAmplitude", F.Id("psi"), F.Id("H")), Num(0))))));

    private static Formula ClaimFormula()
    {
        Formula psi = F.Id("psi"), h = F.Id("H");
        Formula coefficient = new Formula.Binary(
            new Formula.Power(Parenthesized(Call("moment", psi, h, Num(1))), Num(2)),
            FormulaBinaryOperator.Subtract, Call("moment", psi, h, Num(2)));
        Formula positive = new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, coefficient);
        return Disp(Iff(F.Id("claim"), Data(Implies(Eqn(Call("norm", psi), Num(1)),
            Implies(Call("IsHermitian", h), positive)))));
    }
}
