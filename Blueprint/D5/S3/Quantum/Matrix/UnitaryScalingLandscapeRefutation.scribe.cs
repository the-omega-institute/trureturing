using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class UnitaryScalingLandscapeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/devos2014scalingunitary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unitary matrix of order three has a nonglobal local scaling minimum.",
        H("A nonglobal local minimum of the unitary scaling landscape"), Blocks(
            Paragraph(Text("Let i be the imaginary unit. A phase point x=(λ,ρ) consists of two real "
                + "vectors indexed by Fin n. Diagonal unitary scaling gives B with entries "
                + "Bⱼₖ=exp(i(λⱼ+ρₖ))Aⱼₖ. Write sum(B) for the sum of all entries, and "
                + "Ψ_A(x)=landscape A x. The phase space has its usual product topology.")),
            Entry("scaling-sum", "scalingSum", "The sum after diagonal scaling", ScalingSumFormula(),
                "The double sum is sum(B). It is defined for every complex square matrix A and "
                + "every pair of real phase vectors, without a unitarity hypothesis. "
                + "De Vos and De Baerdemacker, Scaling a unitary matrix, Appendix B, "
                + "define Bⱼₖ=exp(i(λⱼ+ρₖ))Aⱼₖ and use this sum in their landscape.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("landscape", "landscape", "The scaling landscape", LandscapeFormula(),
                "Appendix B defines Ψ_A(λ,ρ)=n²−|sum(B)|². Here the same expression is "
                + "defined for every A; the conjecture restricts A to the unitary group. "
                + "The absolute value is the complex modulus.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("claim", "claim", "Every local minimum is global", ClaimFormula(),
                "The assertion quantifies over every natural n, including zero, every complex "
                + "n×n matrix A, and every phase point x. If A is unitary and x is a local minimum "
                + "of Ψ_A in the sense of IsLocalMin, then Ψ_A(x)≤Ψ_A(y) for every phase point y. "
                + "This expresses the absence of nonglobal local minima in Appendix B: "
                + "“We conjecture that all these stationary points are either maxima or saddle points "
                + "or global minima. In other words: we conjecture that no local minima exist.” "
                + "Section 2 likewise conjectures that stationary points with 0<Ψ<n² are saddle "
                + "points. The separate assertion that global minima have Ψ=0 is not part of claim.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A unitary counterexample of order three",
                Disp(Seq(Neg, Sp, V("claim"))),
                "Take A=(1/34)[[−2,24,24],[24,1+17i,1−17i],[24,1−17i,1+17i]]. "
                + "Direct multiplication gives A*A=I, where A* is the conjugate transpose, so A "
                + "is unitary. At the zero phase point, sum(A)=49/17 and "
                + "Ψ_A(0)=9−(49/17)²=200/289. Use one-based indices for the three coordinates. "
                + "The set U={ (λ,ρ) : |ρ₂−ρ₃|<1/50 } is an open neighbourhood of zero. "
                + "For zₖ=exp(iρₖ), the triangle inequality and the row-modulus estimate give "
                + "|sum(B)|≤Σⱼ|(Az)ⱼ|≤49/17 on U, hence Ψ_A≥200/289 there. "
                + "Thus zero is a local minimum. For the comparison, choose "
                + "ρ=(0,2π/3,π/3) and align the row phases by λⱼ=−arg((Az)ⱼ). "
                + "The squared row moduli are 433/289, 217/289−√3/34, and 217/289+√3/34. "
                + "Their moduli are at least 6/5, 4/5, and 8/9, respectively, so the aligned "
                + "sum satisfies |sum(B)|=Σⱼ|(Az)ⱼ|≥26/9>49/17. Consequently this phase point "
                + "has Ψ_A<200/289, and the local minimum at zero is not global. "
                + "This counterexample refutes the landscape conjecture of De Vos and "
                + "De Baerdemacker. It does not refute the existence of a scaling with Ψ_A=0.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ScalingSumFormula()
    {
        Formula n = V("n"), a = V("A"), j = V("j"), k = V("k");
        Formula exponent = Multiply(V("i"), Parenthesized(Add(App(LambdaLower, j), App(Rho, k))));
        Formula sum = Seq(new Formula.Subscript(Sum, Member(j, Fin(n))),
            new Formula.Subscript(Sum, Member(k, Fin(n))), Sp,
            Multiply(App(Exp, exponent), Call("A", j, k)));
        return Disp(All(n, Nat(), All(a, Matrix(n), All(LambdaLower, Vector(n),
            All(Rho, Vector(n), Equal(Call("scalingSum", a, Pair(LambdaLower, Rho)), sum))))));
    }

    private static Formula LandscapeFormula()
    {
        Formula n = V("n"), a = V("A"), x = V("x");
        return Disp(All(n, Nat(), All(a, Matrix(n), All(x, PhaseSpace(n),
            Equal(Call("landscape", a, x), Subtract(new Formula.Power(n, D(2)),
                new Formula.Power(new Formula.Absolute(Call("scalingSum", a, x)), D(2))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = V("n"), a = V("A"), x = V("x"), y = V("y");
        Formula unitary = Member(a, App(Seq(Operatorname, Grp(V("Matrix"), Dot, V("unitaryGroup"))),
            Fin(n), Complex()));
        Formula local = Call("IsLocalMin", Call("landscape", a), x);
        Formula global = new Formula.Relation(Call("landscape", a, x),
            FormulaRelationOperator.LessThanOrEqual, Call("landscape", a, y));
        return Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All(n, Nat(), All(a, Matrix(n), Imp(unitary,
                All(x, PhaseSpace(n), Imp(local, All(y, PhaseSpace(n), global)))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex());
    private static Formula Vector(Formula n) => Seq(Fin(n), Sp, To, Sp, Real());
    private static Formula PhaseSpace(Formula n) =>
        Seq(Parenthesized(Vector(n)), Sp, Times, Sp, Parenthesized(Vector(n)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
