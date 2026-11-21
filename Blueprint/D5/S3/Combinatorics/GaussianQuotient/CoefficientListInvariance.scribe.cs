using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GaussianQuotient;

internal sealed class CoefficientListInvarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/okada2020merged");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplying a polynomial by q^s or substituting q -> q^k with k at least one preserves its ordered list of nonzero coefficients, and hence almost palindromicity.",
        H("Invariance of the nonzero-coefficient list"),
        Blocks(
            Node("coefficient-list", "The ordered nonzero-coefficient list", "coeffList",
                Disp(Equal(Call("coeffList", F.Id("f")), Call("map", Call("coeff", F.Id("f")), Call("sort", Call("support", F.Id("f")))))),
                "coeffList f is the list of the coefficients of f at its support, read in increasing order of exponent; for f in Z[q] these are the f_(lambda_1),...,f_(lambda_kappa) of Definition 9.52, and OkadaPreMergedNonPalindromic.IsAlmostPalindromic f says that this list is a palindrome.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coefficient-list-invariance", "Shifts and substitutions keep the list", "result", ResultFormula(),
                "For every polynomial f over a semiring and every s, the support of q^s f is the support of f shifted by s, and the coefficient of q^s f at n+s is that of f at n; since n -> n+s is strictly increasing it commutes with sorting, so coeffList(q^s f)=coeffList f. Over a commutative semiring and for k at least one, the support of f(q^k) is k times the support of f and the coefficient of f(q^k) at kn is that of f at n, so likewise coeffList(f(q^k))=coeffList f. No hypothesis f nonzero is needed: the zero polynomial has the empty list. Over Z these identities give that q^s f and f(q^k) are almost palindromic exactly when f is. The invariance is stated in the request as the remark after Definition 9.52(1) of Okada, arXiv:2003.02112v2, page 94, defining almost palindromic q-polynomials; it is elementary, and the proof here is repo-derived.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var f = F.Id("f");
        var s = F.Id("s");
        var k = F.Id("k");
        var shift = Multiply(Pow(F.Id("q"), s), f);
        var sub = Call("expand", k, f);
        var shiftList = All("s", Nat(), Equal(Call("coeffList", shift), Call("coeffList", f)));
        var subList = All("k", Nat(), Imp(Le(D(1), k), Equal(Call("coeffList", sub), Call("coeffList", f))));
        var palin = All("k", Nat(), Imp(Le(D(1), k), And(Iff(AP(shift), AP(f)), Iff(AP(sub), AP(f)))));
        return Disp(And(shiftList, And(subList, palin)));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula AP(Formula f) => Call("IsAlmostPalindromic", f);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
