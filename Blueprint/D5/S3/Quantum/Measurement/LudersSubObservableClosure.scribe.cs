using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class LudersSubObservableClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/LudersSubObservableClosure.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/gudder2023dual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-outcome qubit Luders instrument maps an effect to a sub-observable whose double is still a sub-observable but is outside the image of effects. This proves Gudder's conjecture after Theorem 3.1 and answers the arbitrary Luders question in Example 3 negatively.",
        H("A Luders image without ambient Sob sum closure"),
        Blocks(
            Node("subobservable", "Finite sub-observables", SubObservableFormula(),
                "Section 2, p. 3: \"If Δ ↦ A(Δ) is countably additive but A(Ω_A) need not be I, then A is called a sub-observable.\" Here H is Fin d → ℂ, the outcomes are Fin n with all events, and A(Δ) is the sum of A x over x in Δ. Each outcome is positive semidefinite and the total is at most the identity.",
                "IsSubObservable", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sob", "Sob effect algebras", SobFormula(),
                "Section 3, p. 11: \"Let U ⊆ Sob(H) and assume that all elements of U have the same outcome set (Ω, F). We call U a Sob effect algebra if: (S1) there exists an observable Z ∈ U, (S2) if A ∈ U then A′ = Z − A ∈ U, (S3) if A, B ∈ U and A + B ∈ Sob(H), then A + B ∈ U.\" The same Z occurs in (S1) and (S2). In the finite representation, an observable is a sub-observable whose total is 1; addition and subtraction are pointwise on outcome values.",
                "IsSobEffectAlgebra", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("image", "The image of effects under a Luders instrument", ImageFormula(),
                "Section 2, pp. 4–5: \"The dual instrument satisfies L*_x(b) = a_x^(1/2) b a_x^(1/2) for all x ∈ Ω_A, b ∈ E(H).\" The matrices K x are the positive square roots of the instrument's effects. The image consists of families A for which one effect a simultaneously gives A x = K x * a * K x at every outcome x.",
                "ludersImage", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Universal closure for Luders images", ClaimFormula(),
                "After Theorem 3.1, p. 11: \"If I ∈ In(H) and U_I = {I*_a : a ∈ E(H)}, then we conjecture that U need not be a Sob effect algebra.\" Example 3, p. 14: \"If L_x(ρ) = a_x ∘ ρ is an arbitrary Lüders instrument, we do not know whether U_L is a Sob effect algebra. However, in the case where a_x are projections (we then call L sharp) we can show that it is.\" The displayed assertion is universal Sob closure for finite Luders instruments: d is the Hilbert-space dimension, n is the number of outcomes, K x is positive semidefinite, and the sum of K x * K x is 1. Its negation gives a finite counterexample to that closure and therefore proves the existential conjecture.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "An unsharp qubit image violates (S3)",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take K_0 = diag(4/5, 3/5), K_1 = diag(3/5, 4/5), E = (1/400)[[151, 50], [50, 151]] and A x = K x * E * K x. Writing Pplus = Matrix.vecMulVec (1, 1) (star (1, 1)) and Pminus = Matrix.vecMulVec (1, −1) (star (1, −1)), E = (201/800) Pplus + (101/800) Pminus and 1 − E = (199/800) Pplus + (299/800) Pminus show that E is an effect. Each doubled outcome is positive semidefinite; the complement of their total is (1/400) Pplus + (97/400) Pminus. Hence A + A is a sub-observable. If A + A had an effect preimage, its outcome 0 and invertibility of K_0 would force the preimage E + E. The quadratic form of 1 − (E + E) on (1, 1) is −1/100, contradicting positivity. Thus (S3) fails. The summed map contracts off-diagonal entries by 24/25, while the individual invertible outcome fixes the preimage. Example 3's closure for projection effects survives, and no assertion about every unsharp instrument follows.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gudder-2023-sob-effect-algebra-luders"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("gudder-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula value) => Call("Fin", value);
    private static Formula MatrixOf(Formula d) => Call("Matrix", FinOf(d), FinOf(d), Complexes());
    private static Formula FamilyOf(Formula d, Formula n) => Seq(FinOf(n), Sp, To, Sp, MatrixOf(d));
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula Psd(Formula value) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix")), Dot,
            Operatorname, Grp(F.Id("PosSemidef"))), [value]);
    private static Formula Total(Formula family, Formula n) =>
        Seq(Sum, Underscore, Grp(F.Id("x"), Colon, Sp, FinOf(n)), Sp,
            Apply(family, F.Id("x")));
    private static Formula FiniteParameters(Formula body) =>
        All("d", Naturals(), All("n", Naturals(), body));

    private static Formula SubObservableFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), a = F.Id("A");
        return Disp(FiniteParameters(All("A", FamilyOf(d, n),
            Iff(Call("IsSubObservable", a),
                And(All("x", FinOf(n), Psd(Apply(a, F.Id("x")))),
                    Psd(Subtract(D(1), Total(a, n))))))));
    }

    private static Formula SobFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), u = F.Id("U");
        Formula a = F.Id("A"), b = F.Id("B"), z = F.Id("Z");
        Formula type = FamilyOf(d, n);
        Formula allSub = All("A", type, Imp(Member(a, u), Call("IsSubObservable", a)));
        Formula observable = And(Call("IsSubObservable", z), Equal(Total(z, n), D(1)));
        Formula complement = All("A", type, Imp(Member(a, u), Member(Subtract(z, a), u)));
        Formula sumClosure = All("A", type, Imp(Member(a, u), All("B", type,
            Imp(Member(b, u), Imp(Call("IsSubObservable", Add(a, b)), Member(Add(a, b), u))))));
        Formula conditions = And(allSub, Some("Z", type,
            And(Member(z, u), And(observable, And(complement, sumClosure)))));
        return Disp(FiniteParameters(All("U", SetOf(type), Iff(Call("IsSobEffectAlgebra", u), conditions))));
    }

    private static Formula ImageFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), k = F.Id("K"), a = F.Id("a"), family = F.Id("A");
        Formula x = F.Id("x"), kx = Apply(k, x);
        Formula function = Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(x, Colon, Sp, FinOf(n))), Sp, Mapsto, Sp,
            Multiply(Multiply(kx, a), kx));
        Formula members = Some("a", MatrixOf(d), And(And(Psd(a), Psd(Subtract(D(1), a))), Equal(family, function)));
        Formula image = Seq(OpenBrace, family, Colon, Sp, FamilyOf(d, n), Sp, Mid, Sp, members, CloseBrace);
        return Disp(FiniteParameters(All("K", FamilyOf(d, n), Equal(Call("ludersImage", k), image))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), k = F.Id("K"), x = F.Id("x");
        Formula kx = Apply(k, x);
        Formula complete = Equal(Seq(Sum, Underscore, Grp(x, Colon, Sp, FinOf(n)), Sp,
            Multiply(kx, kx)), D(1));
        Formula body = FiniteParameters(All("K", FamilyOf(d, n),
            Imp(All("x", FinOf(n), Psd(kx)),
                Imp(complete, Call("IsSobEffectAlgebra", Call("ludersImage", k))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
