using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FiniteAmplitudeBKMRemainderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), a = F.Id("A"), h = F.Id("H"), s = F.Id("s");
        Formula space = Call("HermitianSpace", n);
        Formula bkm = Call("BKM", a, h);
        Formula gap = Sub(
            Add(Div(Call("traceEntropy", Add(a, h)), D(2)),
                Div(Call("traceEntropy", Sub(a, h)), D(2))),
            Call("traceEntropy", a));
        Formula radius = Call("normalizedDirectionNorm", a, h);
        Formula psi = Call("psi", radius);
        Formula kernelIntegral = Call("integral", Call("traceLogKernel", a, h));
        Formula halfLine = Call("Ioi", D(0));
        Formula posDef = Call("PosDef", Call("value", a));
        Formula radiusHypothesis = Lt(radius, D(1));

        Formula bkmIntegral = Eqn(
            gap,
            Div(Call("intervalIntegral", Call("weightedBKMIntegrand", a, h), D(0), D(1)), D(2)));
        Formula logIdentity = Eqn(gap, Neg(Div(kernelIntegral, D(2))));
        Formula integrable = Call("IntegrableOn", Call("traceLogKernel", a, h), halfLine);
        Formula lower = Le(Div(bkm, D(2)), gap);
        Formula upper = Le(gap, Mul(Call("if", Eqn(radius, D(0)), D(1), psi), Div(bkm, D(2))));
        Formula bkmStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space), Bound("H", space)],
            Implies(posDef, Implies(radiusHypothesis, bkmIntegral)));
        Formula logStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space), Bound("H", space)],
            Implies(posDef, Implies(radiusHypothesis, And(logIdentity, integrable))));
        Formula scaledGap = Call("symmetricEntropyGap", a, Call("smul", s, h));
        Formula contraction = Le(scaledGap, Mul(Call("sq", s), gap));
        Formula.BoundVariable[] contractionParams = [Bound("n", F.Id("FiniteType")),
            Bound("A", space), Bound("H", space), Bound("s", F.Id("Real"))];
        Formula positivePaths = And(Call("PosDef", Call("value", Add(a, h))),
            Call("PosDef", Call("value", Sub(a, h))));
        Formula semidefinitePaths = And(Call("PSD", Call("value", a)),
            And(Call("PSD", Call("value", Add(a, h))), Call("PSD", Call("value", Sub(a, h)))));
        Formula scaleHypothesis = Call("MemberOf", s, Call("Icc", D(0), D(1)));
        Formula boundsStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space), Bound("H", space)],
            Implies(posDef, Implies(radiusHypothesis, And(lower, upper))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite-amplitude symmetric entropy gaps admit an exact BKM integral, logarithmic bounds, and square contraction.",
            H("Finite-Amplitude BKM Remainder"),
            Blocks(
                Paragraph(Text(
                    "The carrier is the real self-adjoint subspace of finite complex matrices. "
                    + "For a positive-definite base A and Hermitian direction H, the normalized "
                    + "direction norm is the norm of A^{-1/2} H A^{-1/2}. The hypothesis that this "
                    + "norm is below one makes both finite-amplitude paths positive definite. BKM "
                    + "denotes Re Tr(H logDeriv(A,H)). Put K_u=(A+uI)^{-1/2}H(A+uI)^{-1/2}; "
                    + "traceLogKernel is Re Tr(CFC.log(I-K_u squared)), integrated on (0,infinity). "
                    + "The weighted BKM integrand is (1-v)(BKM(A+vH,H)+BKM(A-vH,H)). "
                    + "psi(r)=-log(1-r squared)/(r squared), with value one at r=0. "
                    + "symmetricEntropyGap(A,H) is (entropy(A+H)+entropy(A-H))/2-entropy(A).")),
                Describe.Lean(
                    DescribeId.Create("symmetric-entropy-gap-integral-bkm"),
                    DeclarationHandle.Create(Owner + "symmetric_entropy_gap_eq_integral_bkm"),
                    H("The symmetric entropy gap is the second-order integral of the two BKM paths"),
                    StatementSource.FromAuthor(Disp(bkmStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "Differentiating trace entropy along A+vH and A-vH gives the BKM quadratic "
                        + "form as the derivative of the path gradient. Twice integrating with the "
                        + "weight 1-v and using the even sign relation for the negative path yields "
                        + "the displayed symmetric gap."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-entropy-gap-integral-log"),
                    DeclarationHandle.Create(Owner + "symmetric_entropy_gap_eq_integral_log"),
                    H("The symmetric gap equals an even resolvent-logarithm integral"),
                    StatementSource.FromAuthor(Disp(logStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "The two BKM path integrals are exchanged by the even resolvent identity. "
                        + "The scalar identity for opposite eigenvalues turns the paired resolvents "
                        + "into -log(1-K_u^2), and the proved interval and half-line integrability "
                        + "justifies the exchange."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-entropy-gap-bkm-bounds"),
                    DeclarationHandle.Create(Owner + "symmetric_entropy_gap_bkm_bounds"),
                    H("The finite-amplitude gap is squeezed by the BKM form and its exact logarithmic envelope"),
                    StatementSource.FromAuthor(Disp(boundsStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "For every spectral value k of the normalized direction, the scalar bounds "
                        + "k squared <= -log(1-k squared) <= psi(r) k squared hold. Summing over "
                        + "the finite spectrum and integrating over the positive half-line produces "
                        + "both inequalities, including the r=0 branch."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-entropy-gap-square-contraction"),
                    DeclarationHandle.Create(Owner + "symmetric_entropy_gap_square_contraction"),
                    H("Positive-definite symmetric entropy gaps contract by the squared scale"),
                    StatementSource.FromAuthor(Disp(All(contractionParams,
                        Implies(posDef, Implies(positivePaths, Implies(scaleHypothesis, contraction)))))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "Positive definiteness of A+H and A-H implies that the normalized direction "
                        + "has norm below one. The scalar inequality -log(1-s squared z)<= "
                        + "s squared (-log(1-z)) lifts through the finite spectrum and the "
                        + "integrable logarithmic remainder to the displayed matrix inequality."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-entropy-gap-square-contraction-psd"),
                    DeclarationHandle.Create(Owner + "symmetric_entropy_gap_square_contraction_psd"),
                    H("The same square estimate holds at semidefinite endpoints"),
                    StatementSource.FromAuthor(Disp(All(contractionParams,
                        Implies(semidefinitePaths, Implies(scaleHypothesis, contraction))))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "Adding epsilon times the identity to the base makes the base and both "
                        + "endpoints positive definite. Continuity of x log(x), including at zero, "
                        + "makes trace entropy continuous on the full Hermitian space. Taking "
                        + "epsilon to zero preserves the inequality without imposing a spectral gap."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The BKM logarithmic derivative and its classical integral representation are "
                    + "attested by Petz. The symmetric finite-amplitude identities, the exact scalar "
                    + "envelope, and the noncommuting matrix assembly are repository-derived.")))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), type);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Div(Formula left, Formula right) =>
        Call("div", left, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Neg(Formula value) => new Formula.Negate(value);
}
