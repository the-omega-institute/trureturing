using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FiniteAmplitudeBKMRemainderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/FiniteAmplitudeBKMRemainder.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), a = F.Id("A"), h = F.Id("H"), r = F.Id("r");
        Formula space = Call("HermitianSpace", n);
        Formula entropy = Call("traceEntropy", a);
        Formula bkm = Call("BKM", a, h);
        Formula gap = Sub(
            Add(Div(Call("traceEntropy", Add(a, h)), D(2)),
                Div(Call("traceEntropy", Sub(a, h)), D(2))),
            Call("traceEntropy", a));
        Formula radius = Call("normalizedDirectionNorm", a, h);
        Formula psi = Call("psi", radius);
        Formula kernelIntegral = Call("integral", Call("negativeTraceLogKernel", a, h));
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
        Formula boundsStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space), Bound("H", space)],
            Implies(posDef, Implies(radiusHypothesis, And(lower, upper))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite-amplitude symmetric entropy gaps admit an exact BKM integral and sharp logarithmic bounds.",
            H("Finite-Amplitude BKM Remainder"),
            Blocks(
                Paragraph(Text(
                    "The carrier is the real self-adjoint subspace of finite complex matrices. "
                    + "For a positive-definite base A and Hermitian direction H, the normalized "
                    + "direction norm is the norm of A^{-1/2} H A^{-1/2}. The hypothesis that this "
                    + "norm is below one makes both finite-amplitude paths positive definite. BKM "
                    + "denotes the resolvent quadratic form obtained from the logarithmic derivative.")),
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
