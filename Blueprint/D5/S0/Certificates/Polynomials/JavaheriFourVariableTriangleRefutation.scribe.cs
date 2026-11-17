using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Polynomials;

internal sealed class JavaheriFourVariableTriangleRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/javaheri2026arrangement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full four-variable square-root triangle prediction is false at a=4, b=1.",
        H("A counterexample to the four-variable square-root triangle prediction"),
        Blocks(
            Paragraph(Text(
                "Javaheri's arXiv:2610.33653v1, Section 8, predicts that the cyclic "
                    + "arrangement inequality in dimension four holds exactly when "
                    + "sqrt(a), sqrt(b), 1 form a triangle. Lemma 4.3 gives a non-strict "
                    + "threshold, so the triangle inequalities here are weak.")),
            Paragraph(Text(
                "Let c=(a+b+1)/2 and x_5=x_1. The claim is: for every real a,b with "
                    + "a>=0 and b>=0, the assertion that every real quadruple with all "
                    + "x_i>=0 satisfies (sum_i x_i)*(sum_i x_i^a*x_(i+1)^b) "
                    + "<=(sum_i x_i^c)^2 is equivalent to the conjunction "
                    + "sqrt(a)<=sqrt(b)+1, sqrt(b)<=sqrt(a)+1, and "
                    + "1<=sqrt(a)+sqrt(b). Each sum runs from i=1 to 4, and the "
                    + "given cyclic order is retained. Powers are Real.rpow, including "
                    + "0^0=1. The source leaves that convention implicit. No parameter "
                    + "or tuple boundary is excluded: zero coordinates, zero exponents, "
                    + "a+b=1, all-zero tuples, and degenerate triangles remain in scope.")),
            Describe.Lean(
                DescribeId.Create("four-variable-square-root-triangle-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.result"),
                H("The full weak triangle characterization is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The theorem states the negation of the complete claim. At "
                            + "a=4, b=1, c=3, the square-root sides are 2,1,1, which "
                            + "satisfy all three weak triangle inequalities. The positive "
                            + "cyclic quadruple (10,9,7,7) has sum 33, cyclic power sum "
                            + "176744, and cube sum 2415. Thus the left side is 5832552 "
                            + "and the right side is 5832225, a strict excess of 327. "
                            + "The triangle-to-inequality implication therefore fails. "
                            + "All coordinates and exponents used here are positive.")),
                    Paragraph(Text(
                        "Proposition 3.1 gives sufficiency on the smaller linear "
                            + "region b<=a+1, a<=b+1, 1<=a+b; the parameter pair (4,1) "
                            + "lies outside that region. Theorem 1.2 supplies a necessary "
                            + "second-variation condition, identified with the weak "
                            + "square-root triangle region in Lemma 4.3. Necessity "
                            + "does not supply sufficiency. This result establishes "
                            + "failure of the weak characterization at its degenerate "
                            + "boundary; it asserts no strict-interior characterization "
                            + "or corrected validity region."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("javaheri-2026-four-variable-square-root-triangle-refutation"),
                    ResolutionKind.Refuted))),
        []));
}
