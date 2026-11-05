using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AnalyticPickHankelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/AnalyticPickHankel";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/donoghue1974monotone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real boundary limits of analytic matrix Pick kernels give a normalized Hankel inequality.",
        H("Analytic boundary Hankel positivity"), Blocks(
        Item("real_two_point_loewner_posSemidef", "The real two-point Loewner block",
            "Let T be holomorphic on the entire upper half-plane with nonnegative Hermitian "
            + "imaginary part. At distinct real x,y suppose T is complex differentiable "
            + "and Hermitian on a real neighborhood of each point. Then the block matrix "
            + "with diagonal blocks T prime(x), T prime(y), and both off-diagonal blocks "
            + "(T(x)-T(y))/(x-y), is positive semidefinite. Hermitian derivatives follow "
            + "from limits of actual real Hermitian slopes. Along x+i epsilon, the real "
            + "derivative is i times T prime(x); the diagonal Pick quotient is exactly "
            + "(-i/2)(r_epsilon-r_epsilon star), with r_epsilon the actual real slope. "
            + "Off-diagonal limits use ordinary continuity and x not equal to y. "
            + "The global finite Pick theorem and closedness of the positive cone finish."),
        Item("normalizedCoefficient", "Normalized actual derivatives",
            "The coefficient c_k is the actual kth iterated complex derivative of T at zero "
            + "divided by k factorial. In particular c_1=T prime(0), c_2=T double prime(0)/2 "
            + "and c_3=T triple prime(0)/6. These are not independently chosen matrix jets.", true),
        Item("normalized_hankel_posSemidef", "The normalized third-order Hankel block",
            "For every finite complex matrix dimension, assume T is holomorphic on the "
            + "entire upper half-plane with nonnegative Hermitian imaginary part, is "
            + "complex analytic at zero, and is Hermitian on some real neighborhood of "
            + "zero. Then the block matrix with rows (c_1,c_2) and (c_2,c_3) is positive "
            + "semidefinite. First take the real two-point Loewner block at 0,h. With "
            + "B_h=(T(h)-T(0))/h and A=T prime(0), the congruence by the block matrix "
            + "with rows (I,-I/h) and (0,I/h) gives blocks A, (B_h-A)/h, and "
            + "(A-2 B_h+T prime(h))/h squared. Analytic Taylor factorizations of T "
            + "through degree three and of T prime through degree two give exact "
            + "remainder identities: the off-diagonal block is c_2+h c_3+h squared F(h), "
            + "and the bottom block is c_3+h(H(h)-2F(h)). The remainder functions are "
            + "analytic near zero. Continuity and closedness give the Hankel limit. "
            + "No kernel positivity, representing measure or Taylor conclusion is assumed."),
        Paragraph(Text("This is the classical boundary confluence mechanism of Pick and "
            + "Loewner theory, with factorial normalization preserved; see Donoghue, "
            + "DOI 10.1007/978-3-642-65755-9. Global holomorphy and upper-half-plane "
            + "positivity are distinct from the local analytic and real Hermitian "
            + "extension at zero. To use the theorem for an actual principal fractional "
            + "power of a noncommuting matrix pencil, the global analytic and sector "
            + "supplier and its identification with that power remain separate proof "
            + "obligations. No novelty or full independent X,Y He–Saunderson–Fawzi "
            + "compatibility conclusion is asserted.")),
        Paragraph(Text("The two typed dependent-family Reg attempts compile, but their "
            + "source-selection bindings remain unfinished (IE-C050, "
            + "source.selection_missing). See https://github.com/the-omega-institute/"
            + "trureturing/issues/23333. Registration acceptance is not claimed.")))));

    private static DocumentBlock Item(string name, string title, string text, bool definition = false) =>
        Describe.Lean(DescribeId.Create("analytic-hankel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(text))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
