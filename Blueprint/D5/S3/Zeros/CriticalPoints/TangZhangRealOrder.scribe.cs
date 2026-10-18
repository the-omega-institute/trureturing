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
                "The source is Q. Tang and T. Zhang, Sharp Schoenberg type inequalities "
                + "and the de Bruin–Sharma problem, arXiv:2508.10341v3, Conjecture 1.13. "
                + "Its locator and mathematical statement are supplied by the task brief. "
                + "No independent current literature search or priority claim is asserted.")),
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
                DescribeId.Create("tang-zhang-real-order-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The inequality and its equality boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Disp(Inequality),
                    Paragraph(Text(
                        "The first conjunct asserts the displayed bound for every natural "
                        + "n at least one, every nonzero complex family z, and every real p "
                        + "at least one. The second asserts the following equivalence for "
                        + "every such family and every real p greater than one.")),
                    Disp(EqualityCriterion),
                    Paragraph(Text(
                        "The third conjunct negates the universal equality equivalence at "
                        + "p=1. It is witnessed by n=2 and z=(1,2), whose critical points "
                        + "are 1−sqrt(3)/3 and 1+sqrt(3)/3. Their reciprocal norm sum is "
                        + "3, equal to 2 times (1+1/2), although the nonzero roots differ. "
                        + "This refutes the source's endpoint equality clause while retaining "
                        + "the conjectured inequality at that endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tang-zhang-real-order-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The sharp bound with the corrected equality range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
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
                    ResolutionKind.Proved)))));
}
