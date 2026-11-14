using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA186335FiveTermRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2015a186335");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula SumOf(params Formula[] fs) => fs.Aggregate(Add);
    private static Formula All(Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("n"), Nat, body);
    private static Formula Choose(Formula x, Formula y) => Call("choose", x, y);
    private static Formula Cast(Formula x) => Par(Seq(x, Colon, Z));
    private static Formula SourceSum()
    {
        Formula n = F.Id("n"), k = F.Id("k"), j = F.Id("j");
        Formula m = Subtract(Subtract(n, k), j);
        Formula summand = Product(Cast(Choose(Subtract(k, j), m)), Cast(Choose(k, j)),
            Cast(Choose(Multiply(Num(2), m), m)));
        Formula domain = Seq(Par(Seq(k, Comma, j)), InMacro, Call("sourcePairs", n));
        return All(Equal(Call("a", n), Seq(new Formula.Subscript(F.Sum, domain), summand)));
    }
    private static Formula Recurrence()
    {
        Formula n = F.Id("n"), zn = Cast(n);
        Formula An(int lag) => Call("a", lag == 0 ? n : Subtract(n, Num(lag)));
        Formula equation = Equal(SumOf(Product(zn, An(0)),
            Product(Par(Subtract(Num(1), Multiply(Num(2), zn))), An(1)),
            Product(Num(5), Par(Subtract(Num(1), zn)), An(2)),
            Product(Num(3), Par(Subtract(Multiply(Num(2), zn), Num(3))), An(3)),
            Product(Num(5), Par(Subtract(zn, Num(2))), An(4))), Num(0));
        return All(new Formula.Logic(new Formula.Relation(Num(4),
            FormulaRelationOperator.LessThanOrEqual, n), FormulaLogicOperator.Implies, equation));
    }
    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a186335-" + name), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent source double sum A186335 satisfies Mathar's five-term recurrence.",
        H("Mathar's A186335 five-term recurrence"),
        Blocks(
            Node("a", "The exact finite source sum", SourceSum(), AssessedProvenance.FromLiterature(Source),
                "The domain sourcePairs(n) consists of natural pairs (k,j) in range(n+1) squared "
                + "with j ≤ k, k+j ≤ n and n-k-j ≤ k-j. Put m=n-k-j. These conditions give "
                + "0 ≤ j ≤ k ≤ n and 0 ≤ m ≤ k-j before any natural subtraction is interpreted. "
                + "Every excluded pair contributes zero. choose is the ordinary nonnegative binomial "
                + "coefficient; each factor is cast to the integers. No negative central-binomial index "
                + "is evaluated. The sequence is defined by this sum independently of the recurrence.", DescribeRole.Definition),
            Node("claim", "The full source-identified assertion",
                new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Recurrence()),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A186335 attributes the five terms to R. J. Mathar. Its offset is zero and "
                + "the recurrence onset is omitted. Here every natural n ≥ 4 is included, so all five "
                + "indices are nonnegative. Coefficient polynomials and sequence values lie in the integers. "
                + "This is also the integer-index assertion under the usual identification of nonnegative indices. "
                + "The support and onset conventions are explicit source interpretation, with no extra hypothesis.", DescribeRole.Definition),
            Node("result", "The complete recurrence", Recurrence(), AssessedProvenance.FromRepo(Source),
                "Reindex by m=n-k-j and j, with inverse k=n-m-j and support 2m+2j ≤ n. "
                + "Binomial multiplication and formal coefficient substitution identify the source series "
                + "with B*C(X²*B), where B=(1-X-X²)^(-1) and C is the central-binomial series. "
                + "The source-to-series identity is proved from the finite sum. The identity (1-4X)*C'=2*C, "
                + "inverse differentiation and the chain rule then give P*A'+Q*A=0 with "
                + "P=1-2X-5X²+6X³+5X⁴ and Q=-1-5X+9X²+10X³. The existing frozen "
                + "A308815DFiniteRecurrence.euler_coeff and four coefficient shifts yield exactly the displayed "
                + "integer recurrence. No assumed generating function, finite-prefix check or recurrence-defined "
                + "substitute is used. This unit makes no claim about another Mathar sequence, global novelty "
                + "or sibling conjectures.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar-a186335-five-term-recurrence"),
                    ResolutionKind.Proved)))));
}
