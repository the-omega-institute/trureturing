using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class NormalModulusTriangleConstantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/bourinlee2026symmetricmodulus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian pair in dimension two rules out every normal-modulus triangle constant below one quarter.",
        H("The normal-modulus triangle constant in dimension two"),
        Blocks(
            SourceQuotation(),
            Entry("modulus", "IsModulus", "Positive modulus", Modulus(),
                "For complex 2×2 matrices X and P, IsModulus X P requires P to be positive semidefinite "
                + "and P²=X*X. Here X* is the conjugate transpose. The characterization “the positive square "
                + "root is unique” is quoted, not proved or used: the proof checks both conditions for each explicit P.",
                DescribeRole.Definition, true),
            Entry("normal", "IsNormalMatrix", "Normal matrices", Normal(),
                "IsNormalMatrix X means X*X=XX*. The witness matrices are Hermitian and therefore normal.",
                DescribeRole.Definition, true),
            Entry("constant-claim", "claim", "A constant smaller than one quarter", Claim(),
                "The claim asserts the existence of a real c<1/4 working for every normal complex 2×2 pair A,B. "
                + "For every PA,PB,PS satisfying IsModulus A PA, IsModulus B PB, and IsModulus (A+B) PS, "
                + "there must be a unitary V making PA+PB+cV(PA+PB)V*−PS positive semidefinite. "
                + "The real c is cast to a complex scalar. This is the smaller-constant assertion associated "
                + "with the question following Corollary 4.2; the source's upper bound at c=1/4 is not formalized here.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "Every smaller constant fails", Disp(Seq(Neg, Sp, V("claim"))),
                "Take A=diag(1,0), M=(1/25)[[9,−12],[−12,16]], and B=−M. "
                + "The matrix M is the projection onto (3,−4)/5. The lemmas modulus_A, modulus_M, and modulus_PS "
                + "give PA=A, PB=M, and PS=(4/5)I. Put D=A+M and x=(1,2). The lemmas d_pos, d_quad, "
                + "ps_quad, and d_upper give D≥0, x*Dx=2, x*PSx=4, and D≤(8/5)I. "
                + "The identity conjugation_quad holds for every matrix V. For unitary V, it and the conjugated positivity certificates give "
                + "0≤q=x*VDV*x≤8. The asserted inequality requires 4≤2+cq. If c≥0, this yields "
                + "4≤2+8c and c≥1/4; if c<0, it yields 4≤2. Both contradict c<1/4. "
                + "Thus the displayed Hermitian pair defeats every unitary for every smaller real constant. "
                + "Together with the source's Corollary 4.2, the lower bound gives the attained best constant "
                + "1/4 in dimension two; that upper bound is a source consequence rather than a theorem of this module. "
                + "As exact mathematical reasoning, A+B=(1/25)[[16,12],[12,−16]] is of reflection type, "
                + "with scalar modulus (4/5)I, whereas D has eigenvalues 2/5 and 8/5. The ratio "
                + "((4/5)−(2/5))/(8/5)=1/4 also governs the Schur version (4.1); that comparison is not formalized. "
                + "Sharpness in Theorem 4.1 for other positive maps between small dimensions and the classification "
                + "of equality cases are not settled by this result. The journal version's text is ASSUMED-UNVERIFIED; "
                + "the quotations refer to arXiv:2602.19607v1, §4.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Bourin and Lee, Triangle inequalities for the operator symmetric modulus, arXiv:2602.19607v1, "
        + "§4, Corollary 4.2, verbatim: “Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary "
        + "V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest "
        + "possible one.” The following paragraph asks verbatim: “However, contrarily to the Schur version "
        + "(4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 "
        + "(what is the best constant for n = 2 ?).”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bourin-lee-2026-normal-modulus-constant-n2"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Adj(Formula a) => Call("conjTranspose", a);
    private static Formula Pos(Formula a) => Call("PosSemidef", a);

    private static Formula Modulus() => Disp(All("X", Mat, All("P", Mat,
        Iff(Call("IsModulus", V("X"), V("P")),
            And(Pos(V("P")), Eq(Mul(V("P"), V("P")), Mul(Adj(V("X")), V("X"))))))));

    private static Formula Normal() => Disp(All("X", Mat,
        Iff(Call("IsNormalMatrix", V("X")),
            Eq(Mul(Adj(V("X")), V("X")), Mul(V("X"), Adj(V("X")))))));

    private static Formula Claim()
    {
        Formula sum = Add(V("PA"), V("PB"));
        Formula conjugate = Mul(Mul(V("V"), Parenthesized(sum)), Adj(V("V")));
        Formula correction = Seq(Call("ofReal", V("c")), Sp, Cdot, Sp, Parenthesized(conjugate));
        Formula conclusion = Ex("V", Mat, And(Call("memUnitaryGroup", V("V")),
            Pos(Sub(Add(sum, correction), V("PS")))));
        Formula moduli = All("PA", Mat, All("PB", Mat, All("PS", Mat,
            Imp(Call("IsModulus", V("A"), V("PA")),
                Imp(Call("IsModulus", V("B"), V("PB")),
                    Imp(Call("IsModulus", Add(V("A"), V("B")), V("PS")), conclusion))))));
        Formula pairs = All("A", Mat, All("B", Mat,
            Imp(Call("IsNormalMatrix", V("A")), Imp(Call("IsNormalMatrix", V("B")), moduli))));
        Formula bound = new Formula.Relation(V("c"), FormulaRelationOperator.LessThan,
            new Formula.Fraction(D(1), D(4)));
        return Disp(Iff(V("claim"), Ex("c", Real, And(bound, pairs))));
    }
}
