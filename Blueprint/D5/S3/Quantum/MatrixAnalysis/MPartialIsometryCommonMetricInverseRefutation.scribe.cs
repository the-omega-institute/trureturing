using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.MatrixAnalysis;

internal sealed class MPartialIsometryCommonMetricInverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/aouichaouibuchalagarcia2026mpartial");
    private const string Question = "Question 6, page 17: “If T is a 2-partial isometry, is 2T∗ − T∗²T the Moore–Penrose inverse of T with respect to some inner product?” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed inverse of a 2-partial isometry need not admit a common inner product.",
        H("A prescribed generalized inverse with no common inner product"),
        Blocks(
            Node("beta", "The alternating operator sum", BetaFormula(),
                "The operator definition preceding equation (2.1), page 2: “For T ∈ B(H) and integer m ≥ 1, define the selfadjoint operator” βₘ(T) := Σₖ₌₀ᵐ (−1)ᵐ⁻ᵏ binom(m,k) T*ᵏTᵏ. The finite sum uses Finset.range (m + 1), so its natural exponents agree with the nonnegative exponents in the paper. The adjoint is computed using the original Hilbert space structure.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("IsMPartialIsometry", "The source operator condition", PartialFormula(),
                "Section 2, page 2: “More generally, T is an m-partial isometry if T βₘ(T) = 0; it is strict if it is not an (m − 1)-partial isometry.” The order restriction m ≥ 1 is included in the predicate.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("candidateInverse", "The fixed inverse proposed in Question 6", CandidateFormula(),
                "Section 6, page 17: “so S = 2T∗ − T∗²T is a generalized inverse for T and ST is the orthogonal projection onto R(T*).” Both occurrences of the adjoint use the original inner product; S stays fixed when the new form is chosen.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("penroseIn", "The four equations for one positive definite form", PenroseFormula(),
                "The Moore–Penrose condition in Question 6, page 17, is expressed by TST = T, STS = S, and symmetry of TS and ST for the same positive definite complex form g. InnerProductSpace.Core supplies the form without replacing the original norm or adjoint. There is no completeness or norm equivalence condition on the new form.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "Question 6", Disp(IffOf(V("claim"), ClaimBody())),
                Question + "H ranges over complex Hilbert spaces, T over bounded complex-linear endomorphisms, and g over positive definite complex inner products on the same vector space. The candidateInverse uses the original adjoints. All four equations use the same g.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "The answer to Question 6 is negative", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For r ≥ 2 take a = sqrt(2 − 1/r), b = (r − 1)/sqrt(r), and T = [[a,0],[b,0]] on EuclideanSpace ℂ (Fin 2). The relations a² + b² = r and a²r = 2r − 1 give IsMPartialIsometry 2 T. With S = candidateInverse T, ST fixes the first coordinate and kills the second. Its symmetry forces the coordinate vectors to be orthogonal for g. Symmetry of TS then forces 2ab p = ab(2 − r) q, where p and q are the squared lengths of those vectors. Positivity contradicts this equation. The proof specializes r to 25.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("abg-" + (name == "IsMPartialIsometry" ? "partial" :
                name == "candidateInverse" ? "inverse" : name == "penroseIn" ? "penrose" : name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("op-abg2606q6"), ResolutionKind.Refuted) : null);

    private static Formula BetaFormula()
    {
        Formula h = V("H"), m = V("m"), t = V("T"), k = V("k");
        Formula coefficient = Multiply(Pow(Typed(Seq(Minus, D(1)), Complex()), Subtract(m, k)),
            Typed(Apply(Q("Nat", "choose"), m, k), Complex()));
        Formula summand = Smul(Parenthesized(coefficient),
            Parenthesized(Multiply(Pow(Adj(t), k), Pow(t, k))));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(k, Sp, InMacro, Sp, Apply(Q("Finset", "range"), Add(m, D(1))))), Sp, summand);
        return Disp(Hilbert(All("m", Naturals(), All("T", Operators(h),
            Equal(Call("beta", m, t), sum)))));
    }

    private static Formula PartialFormula() => Disp(Hilbert(All("m", Naturals(),
        All("T", Operators(V("H")), IffOf(Call("IsMPartialIsometry", V("m"), V("T")),
            And(LE(D(1), V("m")), Equal(Multiply(V("T"), Call("beta", V("m"), V("T"))), D(0))))))));

    private static Formula CandidateFormula() => Disp(Hilbert(All("T", Operators(V("H")),
        Equal(Call("candidateInverse", V("T")), Subtract(Smul(Typed(D(2), Complex()), Adj(V("T"))),
            Multiply(Pow(Adj(V("T")), D(2)), V("T")))))));

    private static Formula PenroseFormula()
    {
        Formula h = V("H"), g = V("g"), t = V("T"), s = V("S");
        Formula x = V("x"), y = V("y");
        Formula Inner(Formula first, Formula second) => Apply(Seq(g, Dot, Word("inner")), first, second);
        Formula Symmetry(Formula product) => All("x", h, All("y", h,
            Equal(Inner(Apply(Parenthesized(product), x), y),
                Inner(x, Apply(Parenthesized(product), y)))));
        Formula body = And(Equal(Multiply(Multiply(t, s), t), t),
            And(Equal(Multiply(Multiply(s, t), s), s),
                And(Symmetry(Multiply(t, s)), Symmetry(Multiply(s, t)))));
        return Disp(All("H", Word("Type"), Instance(Call("NormedAddCommGroup", h),
            Instance(Call("NormedSpace", Complex(), h), All("g", Core(h),
                All("T", Operators(h), All("S", Operators(h),
                    IffOf(Call("penroseIn", g, t, s), body))))))));
    }

    private static Formula ClaimBody() => Hilbert(All("T", Operators(V("H")),
        Imp(Call("IsMPartialIsometry", D(2), V("T")),
            Seq(Exists, Sp, Typed(V("g"), Core(V("H"))), Comma, Sp,
                Call("penroseIn", V("g"), V("T"), Call("candidateInverse", V("T")))))));

    private static Formula Hilbert(Formula body) => All("H", Word("Type"),
        Instance(Call("NormedAddCommGroup", V("H")),
            Instance(Call("InnerProductSpace", Complex(), V("H")),
                Instance(Call("CompleteSpace", V("H")), body))));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Operators(Formula h) => Call("ContinuousLinearMap", Complex(), h, h);
    private static Formula Core(Formula h) => Apply(Q("InnerProductSpace", "Core"), Complex(), h);
    private static Formula Adj(Formula t) => Apply(Q("ContinuousLinearMap", "adjoint"), t);
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Smul(Formula scalar, Formula value) => Seq(scalar, Sp, Cdot, Sp, value);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
}
