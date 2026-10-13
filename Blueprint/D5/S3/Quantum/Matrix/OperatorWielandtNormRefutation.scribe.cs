using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class OperatorWielandtNormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/lin2013operatorkantorovich");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unital 2-positive complex-linear map violates Lin's operator Wielandt product norm bound.",
        H("Lin's operator Wielandt norm conjecture fails"),
        Blocks(
            SourceQuotation(),
            Entry("partial-isometry", "IsPartialIsometry", "Partial isometries", PartialIsometry(),
                "For a complex n×n matrix X, the condition is XX*X=X. Orthogonality of the final "
                + "spaces is expressed separately by X*Y=0: its entries are inner products between "
                + "columns of X and Y, so the two ranges are orthogonal.", DescribeRole.Definition, true),
            Entry("two-positive", "IsUnitalTwoPositive", "Unital 2-positive linear maps", TwoPositive(),
                "The map is complex-linear, sends I to I, and preserves positive semidefiniteness "
                + "of every 2×2 block matrix [[A,B],[B*,C]] by entrywise application. This implies "
                + "positivity by taking B=C=0 and restricting the positive image to its first block. "
                + "Thus the predicate encodes the unital positive maps in the source definition.",
                DescribeRole.Definition, true),
            Entry("norm-bound", "NormLE", "Euclidean operator norm bound", NormBound(),
                "NormLE T c means that every vector v in the complex Euclidean space satisfies "
                + "‖Tv‖≤c‖v‖. Matrix.toEuclideanLin supplies precisely this linear action, so this "
                + "is the induced operator norm inequality.", DescribeRole.Definition, false),
            Entry("conjecture", "claim", "Conjecture 3.4 in finite dimensions", Claim(),
                "The assertion quantifies over all finite dimensions n,k, complex matrices A,X,Y, "
                + "real bounds m,M, and complex-linear maps Φ. It assumes 0<m≤M, A Hermitian, "
                + "mI≤A≤MI, partial isometries X,Y with orthogonal ranges, and a unital 2-positive Φ. "
                + "Both compressed images must have unit determinants, so their inverses are genuine. "
                + "The general source assertion includes this finite-dimensional case; failure here "
                + "refutes Conjecture 3.4.", DescribeRole.Definition, true),
            Entry("refutation", "result", "An exact four-dimensional counterexample",
                Disp(Seq(Neg, Sp, V("claim"))),
                "Take n=k=4, m=1/25, M=13, A=[[9,0,2,0],[0,2,1,0],[2,1,1,0],[0,0,0,1]], "
                + "P=X=diag(1,1,0,0), and Y with entries Y(2,0)=Y(3,1)=1 and all others zero, "
                + "using zero-based indices. Define Φ(Z)=PZP*+YZY*. Exact LDL* certificates have "
                + "diagonals (224/25,49/25,33/9800,24/25) for A−mI and (4,11,120/11,12) for MI−A. "
                + "The lower factor has third row (25/112,25/49,1,0), and the upper factor has third "
                + "row (−1/2,−1/11,1,0); their other rows equal those of I. Positive diagonal congruences "
                + "certify the bounds. The proof checks XX*X=X, YY*Y=Y, and X*Y=0. "
                + "For a positive block M, conjugation by diag(P,P) and diag(Y,Y) gives positive "
                + "summands whose sum is its entrywise Φ-image. PP*+YY*=I gives unitality. "
                + "The images Φ(Y*AY)=I and Φ(X*AX)=diag(9,2,9,2) have determinants 1 and 324. "
                + "Their inverses are I and diag(1/9,1/2,1/9,1/2). The product T consists of two copies "
                + "of G=[[4/9,1],[2/9,1/2]]. For the unit coordinate vector of index 1, "
                + "‖Te₂‖²=5/4>(26244/26569)², whereas the conjectured constant is 26244/26569. "
                + "The hypotheses therefore hold and the norm conclusion fails. "
                + "The order inequality survives: D^(−1/2)CE^(−1)C*D^(−1/2) is bounded above by qI, "
                + "but CE^(−1)C*D^(−1) is a non-normal similarity of it. This mechanism and the "
                + "unbounded parameter family in the companion problem are exact mathematical reasoning, "
                + "not further Lean theorems. Conditional results assuming Conjecture 3.4 retain their "
                + "conditional form and cannot apply that conjecture universally.", DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Minghua Lin, On an operator Kantorovich inequality for positive linear maps, "
        + "J. Math. Anal. Appl. 402 (2013), 127–132; arXiv:1212.5690v1, §3, p. 6, verbatim: "
        + "“Theorem 3.1. [3] Let 0 < m ≤ A ≤ M and let X, Y be two partial isometries on H "
        + "whose final spaces are orthogonal to each other. Then for every 2-positive linear map Φ, "
        + "Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX) ≤ ((M−m)/(M+m))² Φ(X*AX).” "
        + "§3, pp. 6–7, immediately before Conjecture 3.4, verbatim: “Despite the invalidity of (3.6), "
        + "there is some evidence that the following assertion could be true. We have been unable "
        + "to prove (or disprove) it.” §3, p. 7, verbatim: “Conjecture 3.4. Under the same condition "
        + "as in Theorem 3.1. Then for every 2-positive linear map Φ, "
        + "‖Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX)Φ(X*AX)⁻¹‖ ≤ ((M−m)/(M+m))².” "
        + "§3, p. 6, verbatim: “Let Φ be a unital positive linear map between C*-algebras. "
        + "We say that Φ is 2-positive if whenever the 2 × 2 operator matrix [[A, B],[B*, C]] "
        + "is positive, then so is [[Φ(A), Φ(B)],[Φ(B*), Φ(C)]].” "
        + "P. Zhang, Remarks on an operator Wielandt inequality, arXiv:1506.00737, "
        + "describes the conjecture as still open."));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("lin-2013-operator-wielandt-norm-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat(string n) => Call("Matrix", Call("Fin", V(n)), Call("Fin", V(n)), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Adj(Formula a) => Call("adjoint", a);
    private static Formula Inv(Formula a) => Call("inverse", a);
    private static Formula Phi(Formula a) => Call("Phi", a);
    private static Formula Compress(string x, string y) => Mul(Mul(Adj(V(x)), V("A")), V(y));
    private static Formula Constant => new Formula.Power(Parenthesized(new Formula.Fraction(Sub(V("M"), V("m")), Add(V("M"), V("m")))), D(2));
    private static Formula MapType => Call("ComplexLinearMap", Mat("n"), Mat("k"));

    private static Formula PartialIsometry() => Disp(All("n", Nat, All("X", Mat("n"),
        Iff(Call("IsPartialIsometry", V("X")), Eq(Mul(Mul(V("X"), Adj(V("X"))), V("X")), V("X"))))));
    private static Formula TwoPositive() => Disp(All("n", Nat, All("k", Nat, All("Phi", MapType,
        Iff(Call("IsUnitalTwoPositive", V("Phi")), And(Eq(Phi(V("I")), V("I")),
            All("A", Mat("n"), All("B", Mat("n"), All("C", Mat("n"),
                Imp(Call("PosSemidef", Call("fromBlocks", V("A"), V("B"), Adj(V("B")), V("C"))),
                    Call("PosSemidef", Call("fromBlocks", Phi(V("A")), Phi(V("B")), Phi(Adj(V("B"))), Phi(V("C"))))))))))))));
    private static Formula NormBound() => Disp(All("k", Nat, All("T", Mat("k"), All("c", Real,
        Iff(Call("NormLE", V("T"), V("c")), All("v", Call("EuclideanSpace", Complex, Call("Fin", V("k"))),
            Le(Call("norm", Call("apply", V("T"), V("v"))), Mul(V("c"), Call("norm", V("v"))))))))));
    private static Formula Claim()
    {
        Formula product = Mul(Mul(Mul(Phi(Compress("X", "Y")), Inv(Phi(Compress("Y", "Y")))),
            Phi(Compress("Y", "X"))), Inv(Phi(Compress("X", "X"))));
        Formula body = Call("NormLE", product, Constant);
        Formula[] hypotheses = [Lt(D(0), V("m")), Le(V("m"), V("M")), Call("IsHermitian", V("A")),
            Call("PosSemidef", Sub(V("A"), Mul(V("m"), V("I")))),
            Call("PosSemidef", Sub(Mul(V("M"), V("I")), V("A"))),
            Call("IsPartialIsometry", V("X")), Call("IsPartialIsometry", V("Y")),
            Eq(Mul(Adj(V("X")), V("Y")), D(0)), Call("IsUnitalTwoPositive", V("Phi")),
            Call("IsUnit", Call("det", Phi(Compress("Y", "Y")))),
            Call("IsUnit", Call("det", Phi(Compress("X", "X"))))];
        for (int i = hypotheses.Length - 1; i >= 0; i--) body = Imp(hypotheses[i], body);
        return Disp(Iff(V("claim"), All("n", Nat, All("k", Nat, All("A", Mat("n"),
            All("X", Mat("n"), All("Y", Mat("n"), All("m", Real, All("M", Real, All("Phi", MapType, body))))))))));
    }
}
