using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class SchroderIntegralEGFDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/oeis2024a338193");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The EGF coefficients in OEIS A338193 equal Kurkov's two-index recurrence.",
        H("An Integral EGF And Schroeder Rows"),
        Blocks(
            Note("f", "Kurkov's recurrence",
                "Set f(j,0)=1. For positive m, the boundary is "
                + "f(0,m)=f(0,m-1)+m f(1,m-1). For positive j and m, use "
                + "f(j,m)=f(j-1,m)+m(f(j,m-1)+f(j+1,m-1)). "
                + "Recursion first decreases m, then j; all values are natural numbers.",
                AssessedProvenance.FromLiterature(Source)),
            Note("Original", "The original integral equation",
                "A has constant coefficient one and satisfies "
                + "A=1+Integral ((x/A)' / (x/A^2)') dx. Integration is formal, "
                + "with constant term zero, and all series have rational coefficients. "
                + "The inverse series and the derivative in the denominator have "
                + "constant coefficient one.", AssessedProvenance.FromLiterature(Source)),
            Note("original_exists_unique", "Existence and coefficient uniqueness",
                "Write F(j) for the EGF of row j. The recurrence gives "
                + "F(j+1)=F(j)+x(F(j+1)+F(j+2)). Mathlib's large Schroeder series "
                + "R satisfies R=1+xR+xR^2. Induction first on degree and then on j "
                + "proves F(j)=F(0)R^j. The boundary gives B'=F(0) for "
                + "B=F(0)(1-xR), and B has constant term one. Clearing the units "
                + "in the original equation gives (1+x)AA'-2x(A')^2-A^2=0. "
                + "Its constant-one branch is exactly (1-xR)A'=A: the alternative "
                + "factor has constant term minus one. Strong induction on coefficients "
                + "then proves uniqueness, canceling the nonzero rational factor n+1.",
                AssessedProvenance.FromRepo(Source)),
            Note("A", "The series specified by the source equation",
                "Choose the unique series satisfying Original. The selection predicate "
                + "contains only the original integral equation and initial value. "
                + "The recurrence and the coefficient identity are proved separately.",
                AssessedProvenance.FromRepo(Source)),
            Note("A_original", "The defining equation holds",
                "The chosen A satisfies the original integral equation and A(0)=1.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("a338193-egf-coeff-eq-f"),
                DeclarationHandle.Create(Prefix + "egf_coeff_eq_f"),
                H("The coefficient identity"), StatementSource.FromAuthor(CoefficientIdentity()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                "For every natural n at least one, n! times coefficient n of A equals "
                + "f(0,n-1), viewed in the rationals. Uniqueness identifies A with B; "
                + "differentiating shifts the EGF coefficient index by one, and "
                + "B'=F(0) completes the comparison. Thus the identity also proves "
                + "that every positive-index EGF coefficient is a natural number."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a338193-egf-coefficients"),
                    ResolutionKind.Proved)))));

    private static Formula CoefficientIdentity() => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(1), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp,
        F.Id("n"), Bang, Sp, OpenBracket, new Formula.Power(F.Id("x"), F.Id("n")),
        CloseBracket, F.Id("A"), Sp, Eq, Sp,
        new Formula.Apply(F.Id("f"), [D(0), Seq(F.Id("n"), Minus, D(1))])));

    private static DocumentBlock Note(string name, string title, string prose,
        AssessedProvenance provenance) => Describe.Remark(
        DescribeId.Create("a338193-" + (name == "A" ? "series-a" : name.ToLowerInvariant().Replace('_', '-'))),
        DeclarationHandle.Create(Prefix + name), H(title), provenance,
        Blocks(Paragraph(Text(prose))));
}
