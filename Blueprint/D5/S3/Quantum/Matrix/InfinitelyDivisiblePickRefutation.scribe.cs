using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class InfinitelyDivisiblePickRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/johnson2026powersroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Pick function sends a 4×4 strongly infinitely divisible matrix to a matrix with a negative entry.",
        H("Pick functions do not preserve strong infinite divisibility"),
        Blocks(
            SourceQuotation(),
            Entry("sidm", "IsSIDM", "Strong infinite divisibility", Sidm(),
                "For a real n×n matrix A, IsSIDM A requires every entry to be nonnegative, the determinant "
                + "to be a unit, and a nonnegative mth root for every positive integer m. Over the reals the "
                + "unit-determinant condition is equivalent to invertibility, as in Definition 3.25.",
                DescribeRole.Definition, true),
            Entry("pick-function", "pickFun", "Finite-measure Pick function", PickFunction(),
                "The finite-sum instance of Lemma 2.8 is a+bx+Σᵢwᵢ(tᵢx−1)/(tᵢ+x). "
                + "Positive support points tᵢ and nonnegative weights wᵢ represent a positive finitely supported "
                + "measure. The definition records the real-axis values; the source supplies the analytic Pick representation.",
                DescribeRole.Definition, true),
            Entry("pick-calculus", "pickCalc", "Finite-measure matrix calculus", PickCalculus(),
                "Remark 2.9 gives aI+bA+Σᵢwᵢ(tᵢI−(1+tᵢ²)(A+tᵢI)⁻¹) for matrices with spectrum in D. "
                + "The preservation assertion restricts to upper-triangular matrices with positive diagonal, "
                + "whose spectrum is their diagonal and lies in (0, ∞) ⊂ D. Since tᵢ>0, the shifted matrices "
                + "also have positive diagonal and are invertible, so the inverses are genuine matrix inverses.",
                DescribeRole.Definition, true),
            Entry("preservation", "claim", "Preservation of SIDM", Claim(),
                "The assertion quantifies over every finite support, real a and b, positive tᵢ, nonnegative wᵢ, "
                + "and b≥0. It assumes that pickFun is strictly positive for every positive real argument. "
                + "For every dimension n and real SIDM A that is upper triangular with positive diagonal, it requires "
                + "pickCalc to be SIDM. Such matrices have spectrum equal to their diagonal, inside (0, ∞) ⊂ D, "
                + "so Remark 2.9 applies. The general preservation statement in Table 2, row 12, would imply "
                + "this restriction; failure within it therefore refutes the general statement.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "A negative entry in dimension four", Disp(Seq(Neg, Sp, V("claim"))),
                "Take a=1, b=0, t=(1), and w=(1), giving f(z)=2z/(1+z). For x>0 its real value "
                + "2x/(1+x) is positive. Its pole is outside D and Im f(z)=2 Im z/|1+z|², so it is a Pick function "
                + "in Definition 2.7; this complex analytic explanation is not separately formalized here. "
                + "Let N be the 4×4 shift and E(s)=I+sN+(s²/2)N²+(s³/6)N³. Exact multiplication gives "
                + "E(s)E(u)=E(s+u), and induction gives E(s)^m=E(ms). The matrix A=E(1) has determinant 1 "
                + "and nonnegative roots E(1/m) for every positive integer m. It is upper triangular with diagonal 1, "
                + "so its spectrum is {1} ⊂ (0, ∞) ⊂ D and it satisfies the matrix restriction. "
                + "The proof verifies (A+I)C=I for C=(1/2)I−(1/4)N+(1/48)N³ and identifies C with the inverse. "
                + "Then pickCalc=2I−2C=I+N/2−N³/24 has entry −1/24 at (1,4), using one-based indices, "
                + "or (0,3) in Fin 4. This contradicts its required nonnegativity. Table 2, row 12, has answer No. "
                + "The nilpotent power series f[eᴺ]=I+tanh(N/2) explains the zero quadratic coefficient and "
                + "negative cubic coefficient; for the 3×3 shift it gives I+N/2, which is nonnegative. "
                + "This is the first negative entry in this shift family, not a classification of all smaller SIDM matrices. "
                + "A double-precision computation for the Markov generator B=N−diag(1,1,1,0) gives "
                + "f[eᴮ] with row sums 1 and (1,4) entry approximately −0.0219644568959024. It therefore fails "
                + "to be stochastic. This numerical observation is not formalized and has no certified error bound; "
                + "it suggests a negative answer for row 13. Rows 7 and 13 are not settled by this theorem. "
                + "The source quotations bind to arXiv:2609.06298v1; their independent retrieval and any "
                + "exhaustive literature or priority claim are ASSUMED-UNVERIFIED.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Johnson, Mondal, and Tsatsomeros, Powers, Roots, and Positivity, arXiv:2609.06298v1, "
        + "Table 2, Behavior of Matrix Classes under Pick Functions and Fractional Powers, p. 22, row 12, "
        + "verbatim: “Strongly Infinitely Divisible Matrix (SIDM) | Open | Yes”. The note below the table "
        + "states verbatim: “The entries marked Open indicate cases for which preservation under Pick "
        + "functions remains an open question.” The framing question in §1 is verbatim: “Given A ∈ C "
        + "and a Pick function f, is f[A] ∈ C?” Definition 2.7 is verbatim: “Let D := C\\"), Text(
        "(−∞, 0]. A complex function f analytic on D is called a Pick function if ℑf(z) ℑz ≥ 0, ∀z ∈ D”. "
        + "Definition 3.25 is verbatim: “A nonnegative matrix A ∈ Mn(R) is said to be an infinitely "
        + "divisible matrix (IDM) if, for every positive integer m, there exists a nonnegative matrix Km "
        + "such that (Km)^m = A. If, in addition, A is invertible, then A is called a strongly infinitely "
        + "divisible matrix (SIDM).”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("johnson-mondal-tsatsomeros-2026-sidm-pick-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin(string size) => Call("Fin", V(size));
    private static Formula Mat => Call("Matrix", Fin("n"), Fin("n"), Real);
    private static Formula Weights => Seq(Fin("k"), Sp, To, Sp, Real);
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
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Scale(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula At(string function) => Call(function, V("i"));
    private static Formula PickArgs(string function, params Formula[] rest) =>
        Call(function, [V("a"), V("b"), V("t"), V("w"), .. rest]);
    private static Formula Nonnegative(Formula a) =>
        All("i", Fin("n"), All("j", Fin("n"), Le(D(0), Call("entry", a, V("i"), V("j")))));
    private static Formula Shift => Add(V("A"), Scale(At("t"), V("I")));

    private static Formula Sidm() => Disp(All("n", Nat, All("A", Mat,
        Iff(Call("IsSIDM", V("A")), And(Nonnegative(V("A")),
            And(Call("IsUnit", Call("det", V("A"))), All("m", Nat,
                Imp(Lt(D(0), V("m")), Ex("K", Mat,
                    And(Nonnegative(V("K")), Eq(Pow(V("K"), V("m")), V("A"))))))))))));

    private static Formula WithParameters(Formula body) => All("k", Nat,
        All("a", Real, All("b", Real, All("t", Weights, All("w", Weights, body)))));

    private static Formula PickFunction() => Disp(WithParameters(All("x", Real,
        Eq(PickArgs("pickFun", V("x")), Add(Add(V("a"), Mul(V("b"), V("x"))),
            Call("sum", V("i"), Fin("k"), Mul(At("w"), new Formula.Fraction(
                Sub(Mul(At("t"), V("x")), D(1)), Add(At("t"), V("x"))))))))));

    private static Formula PickCalculus() => Disp(WithParameters(All("n", Nat, All("A", Mat,
        Eq(PickArgs("pickCalc", V("A")), Add(Add(Scale(V("a"), V("I")), Scale(V("b"), V("A"))),
            Call("sum", V("i"), Fin("k"), Scale(At("w"),
                Sub(Scale(At("t"), V("I")), Scale(Add(D(1), Pow(At("t"), D(2))),
                    Call("inverse", Shift)))))))))));

    private static Formula Claim()
    {
        Formula output = Call("IsSIDM", PickArgs("pickCalc", V("A")));
        Formula triangular = All("i", Fin("n"), All("j", Fin("n"),
            Imp(Lt(V("j"), V("i")), Eq(Call("entry", V("A"), V("i"), V("j")), D(0)))));
        Formula diagonal = All("i", Fin("n"), Lt(D(0), Call("entry", V("A"), V("i"), V("i"))));
        Formula matrices = All("n", Nat, All("A", Mat, Imp(Call("IsSIDM", V("A")),
            Imp(triangular, Imp(diagonal, output)))));
        Formula positive = All("x", Real, Imp(Lt(D(0), V("x")), Lt(D(0), PickArgs("pickFun", V("x")))));
        return Disp(Iff(V("claim"), WithParameters(Imp(Le(D(0), V("b")),
            Imp(All("i", Fin("k"), Lt(D(0), At("t"))),
                Imp(All("i", Fin("k"), Le(D(0), At("w"))), Imp(positive, matrices)))))));
    }
}
