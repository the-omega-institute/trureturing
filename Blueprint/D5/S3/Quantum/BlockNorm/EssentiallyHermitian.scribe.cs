using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.BlockNorm;

internal sealed class EssentiallyHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/BlockNorm/EssentiallyHermitian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/bourinlee2021inradius");
    private static readonly Formula N = F.Id("n"), X = F.Id("X");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n >= 1, the Euclidean operator-norm inequality for all positive block completions forces the off-diagonal complex n-by-n matrix to be essentially Hermitian. No invertibility or distinct-singular-value assumption is required.",
        H("Bourin–Lee Conjecture 3.3"),
        Blocks(
            Node("EssentiallyHermitian", "Essentially Hermitian matrices", Over(Eq(Call("EssentiallyHermitian", X), Parenthesized(Affine()))),
                "Printed page 6, verbatim: \"If W(T) is line segment, then T is a so-called essentially Hermitian matrix.\" The affine Hermitian expression fixed for this notion is X = α • H + β • 1, where α and β are complex and H is Hermitian. A point is allowed, including α = 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("CompletionBound", "All positive block completions", Over(Eq(Call("CompletionBound", X), Parenthesized(Completion()))),
                "The displayed hypothesis in Conjecture 3.3 uses Matrix.fromBlocks A X (Matrix.conjTranspose X) B and Matrix.PosSemidef. Both norms are the Euclidean operator norm: Matrix.Norms.L2Operator, definitionally the norm of Matrix.toEuclideanCLM. A and B range over all complex n-by-n matrices; positivity supplies their Hermitian and positive properties.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.3", Eq(F.Id("claim"), Parenthesized(Claim())),
                "The source's 2-by-2 array has n-by-n complex matrix blocks, and its X* denotes Matrix.conjTranspose X. The Lean sentence explicitly quantifies every natural n >= 1 and every X; the positivity, universal completion quantifier and affine Hermitian conclusion are encoded by the two preceding definitions.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds in every positive dimension", Claim(),
                "Positive scalar shifts make the two real spectral edges of K X D sum to zero for every Hermitian D. The quantitative rank-one spike estimate forces first normality and then equality of the projected rank-one matrices. A normal matrix with this equality has collinear eigenvalues; unitary diagonalization reconstructs an affine Hermitian expression. The private diagonalization proof is adapted from TauCeti under Apache-2.0, as detailed in the cited note.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bl-essential-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, name == "claim" ? ClaimQuotation(prose) : Blocks(Paragraph(Text(prose))), role, resolution);
    private static BlockSequence ClaimQuotation(string encoding)
    {
        Formula a = F.Id("A"), b = F.Id("B");
        Formula matrix = Seq(Begin, Grp(F.Id("bmatrix")), a, Amp, X, RowBreak,
            Pow(X, F.Star), Amp, b, End, Grp(F.Id("bmatrix")));
        Formula inequality = Le(new Formula.Subscript(Norm(matrix), Infty),
            new Formula.Subscript(Norm(Add(a, b)), Infty));
        return Blocks(Paragraph(
            Text("Printed page 6, Conjecture 3.3, verbatim: \"Let "),
            Math(Member(X, new Formula.Subscript(Seq(Mathbb, Grp(F.Id("M"))), N))),
            Text(". If the inequality "), Math(inequality),
            Text(" holds for all positive block-matrix with "), Math(X),
            Text(" as off-diagonal block, then "), Math(X),
            Text(" is essentially Hermitian.\"")), Paragraph(Text(encoding)));
    }
    private static Formula Index() => Call("Fin", N);
    private static Formula Over(Formula body) => All(N, Nat(), All(X, Mat(Index()), body));
    private static Formula Affine()
    {
        Formula h = F.Id("H");
        return Some(Alpha, Complex(), Some(Beta, Complex(), Some(h, Mat(Index()), And(Hermitian(h), Eq(X, Add(Smul(Alpha, h), Smul(Beta, D(1))))))));
    }
    private static Formula Completion()
    {
        Formula a = F.Id("A"), b = F.Id("B"), block = QCall("Matrix", "fromBlocks", a, X, Adj(X), b);
        return All(a, Mat(Index()), All(b, Mat(Index()), Imp(Positive(block), Le(Norm(block), Norm(Add(a, b))))));
    }
    private static Formula Claim() => All(N, Nat(), Imp(Le(D(1), N), All(X, Mat(Index()), Imp(Call("CompletionBound", X), Call("EssentiallyHermitian", X)))));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Mat(Formula i) => Call("Matrix", i, i, Complex());
    private static Formula Adj(Formula a) => QCall("Matrix", "conjTranspose", a);
    private static Formula Hermitian(Formula a) => QCall("Matrix", "IsHermitian", a);
    private static Formula Positive(Formula a) => QCall("Matrix", "PosSemidef", a);
}
