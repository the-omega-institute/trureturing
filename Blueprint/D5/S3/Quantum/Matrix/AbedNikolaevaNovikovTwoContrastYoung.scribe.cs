using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AbedNikolaevaNovikovTwoContrastYoungDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/abednikolaevanovikov2026traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact relative Young violation with prescribed density and modulus contrasts in every positive even dimension.",
        H("The exact two-contrast Young envelope"),
        Blocks(
            Entry("contrast", "contrast", "Operator Michelson contrast", ContrastFormula(),
                "Section 3.2, page 8: “For a positive invertible operator T on a Hilbert space with "
                + "m = min σ(T), M = max σ(T) let” followed by "
                + "OMC(T) = tanh OLC(T) = (M − m)/(M + m). "
                + "The real spectral extrema are sInf and sSup. Only nonzero positive semidefinite "
                + "matrices enter the value set; the same fraction includes a zero minimum eigenvalue.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("values", "values", "Relative violations for actual triples", ValuesFormula(),
                "Section 3.8, page 12: “The envelope Vₙ(δ) lets the operator variables range over all operators. "
                + "To see how the violation depends on the operators themselves, we also prescribe their contrast. "
                + "For a positive variable A we use OMC(A), for an arbitrary or self-adjoint variable X the "
                + "contrast OMC(|X|) of its modulus (for the Peierls–Bogoliubov inequality, item 16, the variables "
                + "are positive, as in [14]), and we let every operator variable of an item have the same contrast δ′ ∈ [0, 1]:” "
                + "The displayed set is the set inside that supremum for Table 3, item 8. Here delta is δ, "
                + "eta is δ′, and rho is ρ. Matrices A and B are arbitrary, nonzero, and independently oriented. "
                + "The modulus is CFC.abs X = CFC.sqrt (star X * X). The functional is (rho * X).trace; "
                + "Complex.re selects its real value on positive semidefinite arguments. The normalizer is "
                + "the positive average of the two weighted Gram traces. No trace-one condition is imposed on rho.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("claim", "claim", "The conjectured envelope", ClaimDefinition(),
                "Conjecture 11.1, final clause, page 57: “and the lower bound of Proposition 5.22 is the "
                + "two-contrast envelope of item 8 for even n.” Write n = 2r with r ≥ 1. The parameters "
                + "delta and eta denote the source's δ and δ′. Nonemptiness and boundedness are conclusions, "
                + "so the real supremum represents a nonempty bounded set. The endpoints delta = 0, "
                + "eta = 0 and eta = 1 are included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("result", "result", "The exact envelope in every positive even dimension", Disp(ClaimBody()),
                "Four nonnegative trace products of endpoint gaps give a sharp common-trace interval comparison. "
                + "Applied to the actual Gram orbits, it bounds the weighted Young expression in every nonempty "
                + "finite dimension. A unitary polar factor follows from singular value decomposition, including "
                + "singular matrices. In dimension 2r the density with repeated eigenvalues k and 1 and the "
                + "repeated off-diagonal input with entries 1 and ell attain the bound, where "
                + "k = (1 + delta)/(1 - delta) and ell = (1 - eta)/(1 + eta). This is the direct-sum "
                + "construction of Proposition 5.22. The denominator is (1 - eta)² + 2 eta (1 - delta), "
                + "which is strictly positive on the stated domain. Evenness is needed only for attainment. "
                + "No sharp interior odd-dimensional envelope or singular-density extension is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ann2610i8"), ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Parenthesized(Join(args)));
    private static Formula Join(Formula[] args) => args.Length switch
    {
        0 => Seq(),
        1 => args[0],
        _ => Seq(args[0], Comma, Sp, Join(args[1..])),
    };
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("n")), Call("Fin", V("n")), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Adj(Formula a) => App(Q("Matrix", "conjTranspose"), a);
    private static Formula Abs(Formula a) => App(Q("CFC", "abs"), a);
    private static Formula TraceReal(Formula a) =>
        App(Q("Complex", "re"), App(Q("Matrix", "trace"), a));
    private static Formula Gram(Formula a) => Mul(Adj(a), a);
    private static Formula N => Frac(Add(TraceReal(Mul(V("rho"), Parenthesized(Gram(V("A"))))),
        TraceReal(Mul(V("rho"), Parenthesized(Gram(V("B")))))), D(2));
    private static Formula ValueSet(Formula dimension) => Call("values", dimension, V("delta"), V("eta"));
    private static Formula Envelope => Frac(Mul(Mul(D(4), V("delta")), V("eta")),
        Sub(Add(D(1), new Formula.Power(V("eta"), D(2))), Mul(Mul(D(2), V("delta")), V("eta"))));

    private static Formula ContrastFormula()
    {
        Formula spectrum = Call("spectrum", Real, V("T"));
        Formula maximum = Call("sSup", spectrum);
        Formula minimum = Call("sInf", spectrum);
        return Disp(All("n", Nat, All("T", Mat,
            Eq(Call("contrast", V("T")), Frac(Sub(maximum, minimum), Add(maximum, minimum))))));
    }

    private static Formula ValuesFormula()
    {
        Formula conditions = And(App(Q("Matrix", "PosDef"), V("rho")),
            And(Ne(V("A"), D(0)), And(Ne(V("B"), D(0)),
            And(Eq(Call("contrast", V("rho")), V("delta")),
            And(Eq(Call("contrast", Abs(V("A"))), V("eta")),
            And(Eq(Call("contrast", Abs(V("B"))), V("eta")),
            And(Lt(D(0), N), Eq(V("v"), Frac(Sub(TraceReal(Mul(V("rho"),
                Abs(Mul(V("A"), Adj(V("B")))))), N), N)))))))));
        Formula predicate = Ex("rho", Mat, Ex("A", Mat, Ex("B", Mat, conditions)));
        Formula set = Seq(OpenBrace, V("v"), Colon, Sp, Real, Sp, Mid, Sp, predicate, CloseBrace);
        return Disp(All("n", Nat, All("delta", Real, All("eta", Real,
            Eq(ValueSet(V("n")), set)))));
    }

    private static Formula ClaimBody()
    {
        Formula set = ValueSet(Mul(D(2), V("r")));
        Formula conclusion = And(App(Q("Set", "Nonempty"), set),
            And(Call("BddAbove", set), Eq(Call("sSup", set), Envelope)));
        return All("r", Nat, Imp(Le(D(1), V("r")), All("delta", Real,
            Imp(Le(D(0), V("delta")), Imp(Lt(V("delta"), D(1)), All("eta", Real,
                Imp(Le(D(0), V("eta")), Imp(Le(V("eta"), D(1)), conclusion))))))));
    }

    private static Formula ClaimDefinition() => Disp(Eq(V("claim"), Parenthesized(ClaimBody())));
}
