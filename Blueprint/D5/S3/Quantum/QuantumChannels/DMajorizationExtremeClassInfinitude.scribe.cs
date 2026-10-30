using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class DMajorizationExtremeClassInfinitudeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/vomende2022strictpositivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pure qubit has infinitely many extreme D-majorization classes under unitaries commuting with a positive diagonal D.",
        H("Infinitely many extreme classes in matrix D-majorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("d-majorized-by"),
                DeclarationHandle.Create(Prefix + "DMajorizedBy"),
                H("Matrix D-majorization"),
                StatementSource.FromAuthor(Disp(DMajorizedByFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The matrix x is D-majorized by a when a completely positive, trace-preserving complex linear map t "
                    + "sends a to x and fixes the diagonal matrix with entries d(i). MatrixMap is the space of complex "
                    + "linear maps on these square matrices, and IsCPTP requires complete positivity and preservation "
                    + "of the trace of every input matrix. Each real entry d(i) is included in the complex numbers "
                    + "by Complex.ofReal before forming the diagonal. For strictly positive d this is Definition "
                    + "defi_matrix_D_maj in Strict positivity and D-majorization, TeX lines 466–469. "
                    + "The displayed predicate also makes sense for arbitrary real d; it imposes no positivity hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("majorization-set"),
                DeclarationHandle.Create(Prefix + "majorizationSet"),
                H("The matrices reachable from a"),
                StatementSource.FromAuthor(Disp(MajorizationSetFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The majorization set consists of all matrices x that are D-majorized by a. "
                    + "This is the singleton-input case M_D(a) of equation eq:def_MD, TeX lines 926–932. "
                    + "The definition allows every natural dimension n and every initial complex matrix a."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Finitely many extreme unitary classes"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n, strictly positive real vector d and complex matrix a, the assertion asks "
                    + "for a finite set f representing every real extreme point of M_D(a) by conjugation with a "
                    + "unitary matrix u commuting with D. The finite set f is a set of ambient matrices. "
                    + "The real scalar field in Set.extremePoints specifies real convex combinations. "
                    + "This expresses the finiteness question in the Conclusion and Outlook, TeX lines 1058–1064. "
                    + "The quantifier includes n equal to zero; no positive-dimension assumption is added."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qubit with infinitely many extreme classes"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = 2, d = (1/3, 2/3), D = diag(1/3, 2/3) and A = diag(1, 0). "
                        + "For each natural m, including zero, put h = m² + 1 and "
                        + "Pₘ = (1/h)[[m², m], [m, 1]]. The denominator h is nonzero. "
                        + "Let r = 1/√h and s = 1/√2, with these real numbers regarded as complex scalars. "
                        + "Use the three Kraus matrices K₀ = [[mr, 0], [r, 0]], "
                        + "K₁ = [[0, rs], [0, −mrs]] and K₂ = [[0, 0], [0, s]]. "
                        + "Their map Tₘ(X) = ∑ⱼ KⱼXKⱼ* satisfies "
                        + "Tₘ(X) = X₀₀Pₘ + (X₁₁/2)(I − Pₘ + diag(0, 1)), "
                        + "using r² = 1/h and s² = 1/2.")),
                    Paragraph(Text(
                        "The Kraus representation makes Tₘ completely positive. "
                        + "The identity tr(Pₘ) = 1 and the displayed action give "
                        + "tr(Tₘ(X)) = X₀₀ + X₁₁ = tr(X), so it is trace preserving. "
                        + "Substituting A gives Tₘ(A) = Pₘ, and substituting D gives Tₘ(D) = D. "
                        + "Thus every Pₘ lies in M_D(A). Every matrix x in M_D(A) is positive semidefinite "
                        + "and has trace one: a channel taking A to x preserves positivity and trace.")),
                    Paragraph(Text(
                        "A positive semidefinite matrix x of trace one that annihilates the vector (1, −m) "
                        + "must equal Pₘ. Indeed, the two coordinates of x(1, −m) = 0 and Hermitian symmetry "
                        + "give x₀₁ = mx₁₁ and x₀₀ = m²x₁₁. The trace condition then gives hx₁₁ = 1, "
                        + "which determines all four entries.")),
                    Paragraph(Text(
                        "To prove extremality, suppose Pₘ = rx + sy with x, y in M_D(A), real r, s > 0 "
                        + "and r + s = 1. Set v = (1, −m). Direct multiplication gives Pₘv = 0. "
                        + "Consequently r(v*xv) + s(v*yv) = 0. Both quadratic forms are nonnegative, "
                        + "so v*xv = 0. For a positive semidefinite matrix this implies xv = 0. "
                        + "The preceding trace-one calculation gives x = Pₘ, which is the extreme-point condition. "
                        + "Hence every Pₘ is a real extreme point of M_D(A).")),
                    Paragraph(Text(
                        "For any unitary u commuting with D and any matrix y, "
                        + "tr(Duyu*) = tr(Dy): commute u past D and use invariance of trace under unitary conjugation. "
                        + "On the matrices above this invariant is "
                        + "tr(DPₘ) = (m² + 2)/(3(m² + 1)). Equality of its values at m and k, "
                        + "after clearing the nonzero denominators, gives m² = k². "
                        + "Since m and k are natural numbers, m = k. Thus the invariant is injective on this family.")),
                    Paragraph(Text(
                        "Suppose the finiteness assertion holds and apply it to this d and A. "
                        + "It supplies a finite set f, and for each m a matrix y(m) in f and a unitary u(m) "
                        + "commuting with D such that Pₘ = u(m)y(m)u(m)*. If y(m) = y(k), "
                        + "trace invariance gives tr(DPₘ) = tr(DPₖ), hence m = k. "
                        + "The function y is therefore injective. Its preimage of the finite set f is finite, "
                        + "but contains every natural number, contradicting infinitude of the natural numbers."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vom-ende-2022-d-majorization-extreme-class-infinitude"),
                    ResolutionKind.Refuted)))));

    private static Formula DMajorizedByFormula()
    {
        Formula conditions = And(
            At(Qualified("D5", "S3", "QuantumChannels", "CoPRelativeQuantumnessRefutation", "IsCPTP"), X("t")),
            And(Equal(At(X("t"), X("a")), X("x")),
                Equal(At(X("t"), Diagonal()), Diagonal())));
        return Dimensions(All("x", MatrixType(), All("a", MatrixType(),
            IffOf(LocalCall("DMajorizedBy", X("d"), X("x"), X("a")),
                Some("t", At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"),
                    FinOf(X("n")), FinOf(X("n")), Complexes()), conditions)))));
    }

    private static Formula MajorizationSetFormula() => Dimensions(All("a", MatrixType(),
        Equal(Typed(LocalCall("majorizationSet", X("d"), X("a")), At(Qualified("Set"), MatrixType())),
            Seq(OpenBrace, Typed(X("x"), MatrixType()), Sp, Mid, Sp,
                LocalCall("DMajorizedBy", X("d"), X("x"), X("a")), CloseBrace))));

    private static Formula ClaimFormula()
    {
        Formula conjugation = And(
            Equal(Multiply(X("u"), Diagonal()), Multiply(Diagonal(), X("u"))),
            Equal(X("x"), Multiply(Multiply(X("u"), X("y")), At(Qualified("star"), X("u")))));
        Formula representatives = Some("y", MatrixType(), And(Member(X("y"), X("f")),
            Some("u", MatrixType(), And(
                Member(X("u"), At(Qualified("Matrix", "unitaryGroup"), FinOf(X("n")), Complexes())),
                conjugation))));
        Formula extremePoints = At(Qualified("Set", "extremePoints"), Reals(),
            LocalCall("majorizationSet", X("d"), X("a")));
        Formula finiteness = All("a", MatrixType(), Some("f", At(Qualified("Finset"), MatrixType()),
            All("x", MatrixType(), ImpliesOf(Member(X("x"), extremePoints), representatives))));
        Formula positivity = All("i", FinOf(X("n")),
            new Formula.Relation(Typed(D(0), Reals()), FormulaRelationOperator.LessThan, At(X("d"), X("i"))));
        return IffOf(Local("claim"), Dimensions(ImpliesOf(positivity, finiteness)));
    }

    private static Formula Dimensions(Formula body) => All("n", Naturals(),
        All("d", Arrow(FinOf(X("n")), Reals()), body));
    private static Formula Diagonal() => At(Qualified("Matrix", "diagonal"),
        LambdaOf("i", FinOf(X("n")), At(Qualified("Complex", "ofReal"), At(X("d"), X("i")))));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("n")), FinOf(X("n")), Complexes());
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "DMajorizationExtremeClassInfinitude", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
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
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula ImpliesOf(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
