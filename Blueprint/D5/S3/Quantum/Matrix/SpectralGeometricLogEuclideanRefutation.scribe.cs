using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SpectralGeometricLogEuclideanRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiai2025logmajorizationle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive definite matrix pair refutes Hiai's spectral geometric Log-Euclidean comparison.",
        H("The spectral geometric Log-Euclidean comparison fails"),
        Blocks(
            SourceQuotation(),
            Entry("matrix-power", "mpow", "Real matrix powers",
                Definition("mpow", [V("X"), V("p")],
                    Call("cfc", Call("realPowerFunction", V("p")), V("X"))),
                "For a finite complex matrix X and real p, mpow X p is the real continuous "
                + "functional calculus of t↦t^p at X. On positive definite matrices it is the "
                + "usual positive real power. The continuous functional calculus is total; the "
                + "comparison below restricts the inputs to positive definite matrices.",
                DescribeRole.Definition, false),
            Entry("weighted-geometric", "wgm", "Weighted geometric means",
                Definition("wgm", [V("A"), V("B"), V("alpha")],
                    Mul(Mul(Power(V("A"), Half),
                        Power(Mul(Mul(Power(V("A"), NegHalf), V("B")), Power(V("A"), NegHalf)),
                            V("alpha"))), Power(V("A"), Half))),
                "The formula is A^(1/2)(A^(−1/2)BA^(−1/2))^αA^(1/2), with every power "
                + "interpreted by mpow. At α=1/2 this is the geometric mean A#B.",
                DescribeRole.Definition, true),
            Entry("spectral-geometric", "specMean", "Weighted spectral geometric means",
                Definition("specMean", [V("A"), V("B"), V("alpha")],
                    Mul(Mul(Power(Call("wgm", Call("inverse", V("A")), V("B"), Half), V("alpha")),
                        V("A")), Power(Call("wgm", Call("inverse", V("A")), V("B"), Half), V("alpha")))),
                "Equation (2.3) defines Fα(A,B)=(A^(−1)#B)^α A (A^(−1)#B)^α. "
                + "The inverse is the genuine matrix inverse for the positive definite inputs.",
                DescribeRole.Definition, true),
            Entry("power-parameter", "SG", "The power parameter",
                Definition("SG", [V("alpha"), V("p"), V("A"), V("B")],
                    Power(Call("specMean", Power(V("A"), V("p")), Power(V("B"), V("p")),
                        V("alpha")), new Formula.Fraction(D(1), V("p")))),
                "Equation (2.4) applies Fα to A^p and B^p and then takes the 1/p power. "
                + "The claim uses only p>0.", DescribeRole.Definition, true),
            Entry("log-euclidean", "LE", "Log-Euclidean means",
                Definition("LE", [V("alpha"), V("A"), V("B")],
                    Call("cfc", V("exp"), Add(Scale(Sub(D(1), V("alpha")), Call("cfc", V("log"), V("A"))),
                        Scale(V("alpha"), Call("cfc", V("log"), V("B")))))),
                "The real logarithm and exponential are applied through the continuous "
                + "functional calculus. The logarithmic generator is (1−α)log A+α log B.",
                DescribeRole.Definition, true),
            Entry("log-majorization", "LogMajorized", "Log-majorization",
                LogMajorization(),
                "For Hermitian X,Y of size m, LogMajorized requires that for every finite "
                + "index set s there is an index set t of the same cardinality with the product "
                + "of X's eigenvalues indexed by s at most the product of Y's eigenvalues "
                + "indexed by t. It also requires det X=det Y. The formula's eigenvalueProduct "
                + "means this finite product, using the indicated Hermitian proof hX or hY. "
                + "For positive definite matrices this is equivalent to the usual comparison "
                + "of the products of the k largest eigenvalues for each k.",
                DescribeRole.Definition, false),
            Entry("open-case", "claim", "The open case of Problem 3.20", Claim(),
                "The assertion quantifies over all real α>1 and p>0, dimensions m, and "
                + "positive definite complex matrices A,B of size m. For each Hermitian proof "
                + "of each mean, it requires the stated log-majorization. Both means are "
                + "Hermitian on these inputs. The general source assertion includes m=2, "
                + "so a violation in that dimension refutes the open case.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "An exact two-dimensional counterexample",
                Disp(Seq(Neg, Sp, V("claim"))),
                "Take α=2, p=1, A=diag(1,1048576), and "
                + "B=[[272,504],[504,1853]]/125. The orthogonal matrix "
                + "U=[[24,7],[−7,24]]/25 gives B=U diag(1,16) U*, proving positivity. "
                + "Put X=A^(1/2)BA^(1/2), T=77761424/5, K=X+4096I, and H=B+4096A^(−1). "
                + "The exact identity K²=TX and positivity identify X^(1/2)=K/√T. "
                + "Thus L=A^(−1)#B=H/√T, and the identity LAL=B yields "
                + "SG₂,₁=L²AL²=LBL=HBH/T. Its entry of index (0,0) is "
                + "286558676/121502225>2. On the other side, −log A+2log B=(log 2)N, "
                + "where N=[[392,1344],[1344,−7892]]/625. The factorization "
                + "I−N=V diag(233/625,285/233) V*, with V=[[1,0],[−1344/233,1]], "
                + "proves N≤I. The spectral bound and scalar exponential monotonicity imply "
                + "LE₂≤2I, so all its eigenvalues are at most 2. If all SG eigenvalues were "
                + "at most 2, spectral calculus would give SG≤2I, contradicting its diagonal "
                + "entry. Taking the singleton consisting of an SG eigenvalue above 2 "
                + "contradicts log-majorization. Determinant equality is unnecessary. "
                + "The companion problem gives the positive-power reduction and an asymptotic "
                + "family for every α>1 as mathematical reasoning, not additional Lean theorems. "
                + "The sufficient decreasing-power route in Problem 3.20 cannot hold universally "
                + "when combined with the paper's small-power limit to LE; the remaining "
                + "companion questions of Problem 3.12 remain open here.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Fumio Hiai, Log-majorizations between quasi-geometric type means for matrices, "
        + "Linear Algebra Appl. 735 (2026), 123–174; arXiv:2510.04691v3. "
        + "§2, equation (2.3), verbatim: “Fα(A, B) := (A^{−1}#B)^α A(A^{−1}#B)^α.” "
        + "§2, equation (2.4), verbatim: “SGα,p(A, B) := Fα(A^p, B^p)^{1/p}.” "
        + "§2, verbatim: “LEα(A, B) := exp((1 − α) log A + α log B)” and "
        + "“A#αB := A^{1/2}(A^{−1/2}BA^{−1/2})^α A^{1/2}”, with # = #_{1/2}. "
        + "Problem 3.20, verbatim: “Problem 3.20. The case remaining open is whether "
        + "SGα,p ≺log LEα for α > 1. Note that this is affirmative if SGα,p ≺log SGα,q "
        + "if α > 1 and p ≥ q (see Problem 3.12).” "
        + "The summary table after Problem 3.20 has row “SGα,p ≺log LEα”, with entries "
        + "“none” for 0 < α < 1 and “?” for α > 1."));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create((name is "mpow" or "LE"
                ? "D5/S3/Quantum/Matrix/SpectralPower." : Prefix) + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hiai-2026-spectral-geometric-log-euclidean-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("m")), Call("Fin", V("m")), Complex);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula NegHalf => new Formula.Fraction(Sub(D(0), D(1)), D(2));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scale(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Power(Formula a, Formula b) => Call("mpow", a, b);
    private static Formula Definition(string name, Formula[] args, Formula rhs) => Disp(Eq(Call(name, args), rhs));

    private static Formula LogMajorization()
    {
        Formula indexSet = Call("Finset", Call("Fin", V("m")));
        Formula products = All("s", indexSet, Some("t", indexSet,
            And(Eq(Call("card", V("t")), Call("card", V("s"))),
                Le(Call("eigenvalueProduct", V("hX"), V("s")),
                    Call("eigenvalueProduct", V("hY"), V("t"))))));
        Formula body = Iff(Call("LogMajorized", V("X"), V("Y"), V("hX"), V("hY")),
            And(products, Eq(Call("det", V("X")), Call("det", V("Y")))));
        body = All("hY", Call("IsHermitian", V("Y")), body);
        body = All("hX", Call("IsHermitian", V("X")), body);
        return Disp(All("m", Nat, All("X", Mat, All("Y", Mat, body))));
    }

    private static Formula Claim()
    {
        Formula x = Call("SG", V("alpha"), V("p"), V("A"), V("B"));
        Formula y = Call("LE", V("alpha"), V("A"), V("B"));
        Formula body = All("hX", Call("IsHermitian", x), All("hY", Call("IsHermitian", y),
            Call("LogMajorized", x, y, V("hX"), V("hY"))));
        Formula[] hypotheses = [Lt(D(1), V("alpha")), Lt(D(0), V("p")),
            Call("PosDef", V("A")), Call("PosDef", V("B"))];
        for (int i = hypotheses.Length - 1; i >= 0; i--) body = Imp(hypotheses[i], body);
        return Disp(Iff(V("claim"), All("alpha", Real, All("p", Real, All("m", Nat,
            All("A", Mat, All("B", Mat, body)))))));
    }
}
