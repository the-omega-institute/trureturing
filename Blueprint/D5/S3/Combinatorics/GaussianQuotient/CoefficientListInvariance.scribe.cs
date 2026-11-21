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
            Node("coefficient-list", "The ordered nonzero-coefficient list", "supportCoeffList",
                Disp(Equal(Call("supportCoeffList", F.Id("f")), Call("map", Call("coeff", F.Id("f")), Call("sort", Call("support", F.Id("f")))))),
                "supportCoeffList f is the list of the coefficients of f at its support, read in increasing order of exponent; for f in Z[q] these are the f_(lambda_1),...,f_(lambda_kappa) of Definition 9.52, and OkadaPreMergedNonPalindromic.IsAlmostPalindromic f says that this list is a palindrome. In the result, RPoly is R[q] for a semiring R (a commutative semiring for the substitution) and ZPoly is Z[q].",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coefficient-list-invariance", "Shifts and substitutions keep the list", "result", ResultFormula(),
                "For every polynomial f over a semiring and every s, the support of q^s f is the support of f shifted by s, and the coefficient of q^s f at n+s is that of f at n; since n -> n+s is strictly increasing it commutes with sorting, so supportCoeffList(q^s f)=supportCoeffList f. Over a commutative semiring and for k at least one, the support of f(q^k) is k times the support of f and the coefficient of f(q^k) at kn is that of f at n, so likewise supportCoeffList(f(q^k))=supportCoeffList f. No hypothesis f nonzero is needed: the zero polynomial has the empty list. Over Z these identities give that q^s f and f(q^k) are almost palindromic exactly when f is. Okada, arXiv:2003.02112v2, Definition 9.52(1), page 94, defines almost palindromic polynomials; the paper does not state this invariance, and the statement and proof are repo-derived. The support identity for q^s f is transported from Mathlib's AddMonoidAlgebra.support_coeff_single_mul.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var f = F.Id("f");
        var s = F.Id("s");
        var k = F.Id("k");
        var shift = Multiply(new Formula.Power(F.Id("q"), s), f);
        var sub = Call("expand", k, f);
        var shiftList = All("f", Poly(), All("s", Nat(), Equal(Call("supportCoeffList", shift), Call("supportCoeffList", f))));
        var subList = All("f", Poly(), All("k", Nat(), Imp(Le(D(1), k), Equal(Call("supportCoeffList", sub), Call("supportCoeffList", f)))));
        var palin = All("f", IntPoly(), All("s", Nat(), All("k", Nat(), Imp(Le(D(1), k), And(Iff(AP(shift), AP(f)), Iff(AP(sub), AP(f)))))));
        return Disp(And(shiftList, And(subList, palin)));
    }

    private static Formula Poly() => new Formula.NamedConstant(FormulaIdentifier.Create("RPoly"));
    private static Formula IntPoly() => new Formula.NamedConstant(FormulaIdentifier.Create("ZPoly"));

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
