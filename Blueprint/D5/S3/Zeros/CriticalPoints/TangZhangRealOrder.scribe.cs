using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class TangZhangRealOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/CriticalPoints/TangZhangRealOrder";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Zeros/tang2025schoenberg");
    private static Formula P => F.Id("p");
    private static Formula N => F.Id("n");
    private static Formula Sub(Formula value, string index) => Seq(value, Underscore, Grp(F.Id(index)));
    private static Formula Sum(string index, Formula value) => Seq(
        F.Sum, Underscore, Grp(F.Id(index), Eq, D(1)), Caret, Grp(N), Sp, value);
    private static Formula NegativePower(Formula value) =>
        new Formula.Power(new Formula.Absolute(value), Seq(Minus, P));
    private static Formula Left => Sum("k", NegativePower(Sub(F.Id("w"), "k")));
    private static Formula Coefficient => Seq(F.Id("c"), Underscore, Grp(N, Comma, P));
    private static Formula CoefficientFormula => Seq(Coefficient, Eq,
        new Formula.Fraction(Seq(new Formula.Power(Seq(Open, N, Plus, D(1), Close), P),
            Plus, N, Minus, D(1)), N));
    private static Formula Right => Seq(Coefficient, Sp,
        Sum("j", NegativePower(Sub(F.Id("z"), "j"))));
    private static Formula ConstantRoots => Seq(Forall, Sp, F.Id("i"), Comma, F.Id("j"), Comma, Sp,
        Sub(F.Id("z"), "i"), Eq, Sub(F.Id("z"), "j"));
    private static Formula Inequality => Seq(Left, Leq, Sp, Right);
    private static Formula EqualityCriterion => Seq(Open, Left, Eq, Right, Close, Sp, Iff, Sp, ConstantRoots);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal critical-point moment has the sharp Tang–Zhang coefficient for "
        + "every real p at least one. For p greater than one, equality characterizes "
        + "coincident nonzero roots. The conjectured equality characterization at p=1 is false.",
        H("Tang–Zhang's real-order reciprocal critical-point inequality"),
        Blocks(
            Paragraph(Text(
                "Q. Tang and T. Zhang, Sharp Schoenberg type inequalities "
                + "and the de Bruin–Sharma problem, arXiv:2508.10341v3, §1.3, Conjecture 1.13.")),
            Paragraph(Text(@"Conjecture 1.13. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n be the zeros of P′(z). Then for every real number p ≥ 1 we have Σ_{k=1}^n 1/|w_k|^p ≤ ((n+1)^p + n − 1)/n · Σ_{j=1}^n 1/|z_j|^p. Moreover, equality holds if and only if z_1 = ⋯ = z_n.")),
            Paragraph(Text(
                "Let n be at least one, let z_j be nonzero complex numbers, and set "
                + "P(z)=z times the product of z−z_j. Let w_k be the n roots of P′, "
                + "counted with algebraic multiplicity. Repeated z_j are permitted. "
                + "The polynomial definition and reciprocal-root spectral identification "
                + "are reused from TangZhangOrderMinusTwo.")),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-coefficient"),
                DeclarationHandle.Create(Module + ".c"),
                H("The real-order coefficient"),
                StatementSource.FromAuthor(Disp(CoefficientFormula)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The expression is defined for every natural n and real p; "
                    + "the theorem uses n at least one. Real powers are Real.rpow."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 1.13 as stated"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n≥1 and every nonzero complex family z, the conjecture "
                    + "asserts both the sharp moment inequality and equality if and only "
                    + "if all z_j coincide, for every real p≥1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-counterexample"),
                DeclarationHandle.Create(Module + ".counterexample"),
                H("The endpoint equality criterion is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 1.13 is false. For n=2, z=(1,2), and p=1, "
                    + "the critical points are 1−sqrt(3)/3 and 1+sqrt(3)/3. "
                    + "Their reciprocal norm sum is 3, equal to c(2,1) times "
                    + "(1+1/2), although the nonzero roots differ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The inequality and its equality boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Math(Disp(Inequality))),
                    Paragraph(Text(
                        "The first conjunct asserts the displayed bound for every natural "
                        + "n at least one, every nonzero complex family z, and every real p "
                        + "at least one. The second asserts the following equivalence for "
                        + "every such family and every real p greater than one.")),
                    Paragraph(Math(Disp(EqualityCriterion))),
                    Paragraph(Text(
                        "The third conjunct is the literal negation of Conjecture 1.13, "
                        + "including both assertions for every real p≥1. Its refutation is witnessed by n=2 and z=(1,2), whose critical points "
                        + "are 1−sqrt(3)/3 and 1+sqrt(3)/3. Their reciprocal norm sum is "
                        + "3, equal to 2 times (1+1/2), although the nonzero roots differ. "
                        + "This refutes the source's endpoint equality clause while retaining "
                        + "the conjectured inequality at that endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 1.13 is false; the sharp bound and strict-order equality case hold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The result refutes Conjecture 1.13 as stated and proves, in the same conjunction, the sharp inequality for every real p≥1 and the equality equivalence for every real p>1.")),
                    Paragraph(Text("For every n≥1, nonzero complex a and real p, the sum of norm(w)^(−p) over roots of the derivative of P(Z)=Z(Z−a)^n equals c(n,p) times the sum of norm(a)^(−p) over Fin n, where c(n,p)=((n+1)^p+n−1)/n. The derivative has the root a with multiplicity n−1 and the root a/(n+1), including the case n=1.")),
                    Paragraph(Text("It is false that for every natural n and every nonzero complex family z, equality in the reciprocal-norm moment bound at p=1 is equivalent to all z_j being equal. For n=2 and z=(1,2), P′(Z)=3Z²−6Z+2 has roots 1−sqrt(3)/3 and 1+sqrt(3)/3. Both roots are positive, their reciprocal norm sum is 3, and c(2,1) times (1+1/2) is also 3, while 1 and 2 differ.")),
                    Paragraph(Text(
                        "Write b_j=1/z_j, D=diag(b_j), H=I+J, and R=H^(1/2). "
                        + "The characteristic roots of A=RDR are the reciprocal critical "
                        + "points, including multiplicity. The existing order-minus-two "
                        + "module supplies this spectral reduction and unitary Schur "
                        + "triangularization supplies a basis for the actual matrix A.")),
                    Paragraph(Text(
                        "For p greater than one, an entire scalar trace function interpolates "
                        + "the weighted Schur moment. Its left strip boundary is bounded by "
                        + "one; the right boundary is bounded by c(n,p) times the sum of "
                        + "the p-th powers of the moduli of b_j. The explicit complex "
                        + "powers of H use the projection J/n. The three-lines theorem "
                        + "yields the asserted bound for all real p greater than one.")),
                    Paragraph(Text(
                        "Equality at an interior strip point propagates to the right "
                        + "boundary by the maximum modulus principle. Nonorthogonality "
                        + "of the rank-one columns forces the boundary phases to coincide "
                        + "for every imaginary parameter, giving common phase and modulus "
                        + "for the b_j. Conversely, when z_j=a, P′ has the root a with "
                        + "multiplicity n−1 and the root a/(n+1), giving equality directly. "
                        + "The p=1 bound follows from the unitary rank-one trace estimate; "
                        + "the explicit pair (1,2) supplies the endpoint refutation."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tang-zhang-2025-real-order-schoenberg"),
                    ResolutionKind.Refuted)))));
}
