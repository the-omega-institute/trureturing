using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class TangZhangOrderMinusTwoDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Zeros/tang2025schoenberg");
    private static Formula Z => F.Id("z");
    private static Formula Sub(Formula value, string index) => Seq(value, Underscore, Grp(index == "1" ? D(1) : F.Id(index)));
    private static Formula Pow(Formula value) => new Formula.Power(value, D(2));
    private static Formula Sum(string index, Formula value) => Seq(
        F.Sum, Underscore, Grp(F.Id(index), Eq, D(1)), Caret, Grp(F.Id("n")), Sp, value);
    private static Formula Reciprocal(Formula value) => new Formula.Fraction(D(1), value);
    private static Formula LeftSide => Sum("k", Reciprocal(Pow(new Formula.Absolute(Sub(F.Id("w"), "k")))));
    private static Formula RightSide => Seq(D(3), Sum("j", Reciprocal(Pow(new Formula.Absolute(Sub(Z, "j"))))),
        Plus, Pow(new Formula.Absolute(Sum("j", Reciprocal(Sub(Z, "j"))))));
    private static Formula Polynomial => Seq(F.Id("P"), Open, Z, Close, Eq, Z,
        Prod, Underscore, Grp(F.Id("j"), Eq, D(1)), Caret, Grp(F.Id("n")), Sp,
        Open, Z, Minus, Sub(Z, "j"), Close);
    private static Formula Collinear => Seq(Forall, Sp, F.Id("j"), Comma, Sp,
        Exists, Sp, Sub(F.Id("r"), "j"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Sub(Z, "j"), Eq, Sub(F.Id("r"), "j"), Sub(Z, "1"));
    private static Formula Result => Seq(LeftSide, Leq, Sp, RightSide, Comma, Sp,
        Open, LeftSide, Eq, RightSide, Close, Sp, Iff, Sp, Collinear);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tang–Zhang Conjecture 6.3 holds for every finite nonempty family of nonzero "
        + "complex roots, with equality exactly for collinearity through the origin.",
        H("Tang–Zhang's sharp order −2 inequality"),
        Blocks(
            Paragraph(Text("Q. Tang, T. Zhang, \"Sharp Schoenberg type inequalities and the de Bruin–Sharma problem\", arXiv:2508.10341v3 (5 Dec 2025), §6, p. 31.")),
            Paragraph(Text("The identity (5.2) leads us to the following conjectural refinements of Theorem 6.1 in the case of order −2.")),
            Paragraph(Text("Conjecture 6.3. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \\ {0}, and let w_1, …, w_n denote the zeros of P′(z). Then Σ_{k=1}^n 1/|w_k|² ≤ 3 Σ_{j=1}^n 1/|z_j|² + |Σ_{j=1}^n 1/z_j|². (6.9) Moreover, equality in (6.9) holds whenever z_1, …, z_n all lie on the same line passing through the origin.")),
            Paragraph(Text("In the case n = 2 we can verify Conjecture 6.3 by an explicit computation.")),
            Paragraph(Text(
                "The last sentence is Proposition 6.4. Theorem 6.1 in the same source "
                + "has the weaker right side (n+3) times the sum of reciprocal squared root moduli.")),
            Describe.Lean(
                DescribeId.Create("tang-zhang-root-polynomial"),
                DeclarationHandle.Create(Module + ".P"),
                H("The polynomial with a simple root at zero"),
                StatementSource.FromAuthor(Disp(Polynomial)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The polynomial is defined for every natural n and every complex family z. "
                    + "For the conjecture n is at least one and each z_j is nonzero. "
                    + "Repeated nonzero roots are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-order-minus-two-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The inequality and exact equality criterion"),
                StatementSource.FromAuthor(Disp(Result)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every n at least one and every family of nonzero complex z_j, "
                    + "the w_k are all roots of the derivative of P, counted with multiplicity. "
                    + "The displayed inequality holds, and equality is equivalent to every "
                    + "z_j being a real multiple of the first root z_1. "
                    + "Thus the source's sufficient equality condition is also necessary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-order-minus-two-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The sharp inequality with both equality directions"),
                StatementSource.FromAuthor(Disp(Result)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Set b_j=1/z_j, D=diag(b_j), and let J be the all-ones matrix. "
                        + "The inverse critical points, with multiplicity, are precisely the "
                        + "characteristic roots of D(I+J), a rank-one perturbation of D.")),
                    Paragraph(Text(
                        "For the invertible Hermitian square root R of I+J, the similar "
                        + "matrix RDR has squared Frobenius norm exactly equal to the "
                        + "displayed right side. Schur's inequality gives the bound. "
                        + "Its equality criterion becomes conjugate(b_i)b_j=b_i conjugate(b_j), "
                        + "equivalently collinearity of the nonzero z_j through the origin."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tang-zhang-2025-order-minus-two-schoenberg"),
                    ResolutionKind.Proved)))));
}
