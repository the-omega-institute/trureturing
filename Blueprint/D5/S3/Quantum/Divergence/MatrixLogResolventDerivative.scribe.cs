using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MatrixLogResolventDerivativeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/MatrixLogResolventDerivative.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), a = F.Id("A"), h = F.Id("H"), j = F.Id("J");
        Formula s = Call("HermitianSpace", n);
        Formula path = Call("pathDerivativeIntegral", a);
        Formula resolvent = Call("resolventDerivativeIntegral", a);
        Formula hessian = Call("entropyHessian", a);
        Formula hypothesis = Call("PosDef", Call("value", a));
        Formula.BoundVariable[] parameters = [Bound("n", F.Id("FiniteType")), Bound("A", s)];

        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual matrix logarithm has a resolvent derivative, and trace entropy has its BKM Hessian.",
            H("Matrix Logarithm Derivatives and the Trace-Entropy Hessian"),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary finite index type n with decidable equality, M is the space of "
                    + "square complex matrices and S = HermitianSpace(n) is its self-adjoint real "
                    + "subspace. value is the inclusion from S into M. The norm is the L2 operator "
                    + "norm and positivity is the Loewner order. No nonempty-index assumption, "
                    + "trace normalization, or commutativity assumption is imposed. logMap sends "
                    + "Y in S to CFC.log(value(Y)), using the real logarithm in continuous functional calculus.")),
                Paragraph(Text(
                    "Put B(A,u) = (1-u)I + u value(A). pathDerivative(A,u) is the real continuous "
                    + "linear map H to inverse(B(A,u)) value(H) inverse(B(A,u)); "
                    + "pathDerivativeIntegral(A) is its Bochner integral from zero to one. "
                    + "resolventDerivative(A,t) is H to inverse(value(A)+tI) value(H) "
                    + "inverse(value(A)+tI), and resolventDerivativeIntegral(A) is its Bochner "
                    + "integral on the open positive half-line with Lebesgue measure. "
                    + "All inverses in these maps are Ring.inverse.")),
                Describe.Lean(
                    DescribeId.Create("matrix-logarithm-path-frechet-derivative"),
                    DeclarationHandle.Create(Owner + "matrix_log_hasFDerivAt_path"),
                    H("The affine-path integral differentiates the actual logarithm"),
                    StatementSource.FromAuthor(Disp(All(parameters,
                        Implies(hypothesis, Call("HasFDerivAt", Call("logMap", n), path, a))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Positive definiteness supplies a positive scalar d and a neighborhood s "
                            + "of A such that dI is below value(Y) for every Y in s. Thus B(Y,u) is "
                            + "uniformly bounded below by min(1,d)I for all u in [0,1], and the inverse "
                            + "sandwich derivatives have the common norm bound min(1,d) to the power "
                            + "minus two. Differentiation under the parameter integral is valid on "
                            + "this same neighborhood. The matrix-logarithm path representation "
                            + "identifies that integral with the actual CFC logarithm there.")),
                        Paragraph(Text(
                            "The matrix logarithm and its integral differential are classical. "
                            + "The neighborhood control and its connection to the actual CFC.log "
                            + "function are derived here from the spectral lower bound, the "
                            + "self-adjoint norm-order estimate, and dominated differentiation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("matrix-logarithm-resolvent-frechet-derivative"),
                    DeclarationHandle.Create(Owner + "matrix_log_hasFDerivAt_resolvent"),
                    H("The half-line resolvent derivative is integrable and acts as logDeriv"),
                    StatementSource.FromAuthor(Disp(All(parameters,
                        Implies(hypothesis, And(
                            Call("HasFDerivAt", Call("logMap", n), resolvent, a),
                            And(Call("IntegrableOn", Call("resolventDerivative", a), Call("positiveHalfLine")),
                                All([Bound("H", s)], Eqn(Call("apply", resolvent, h),
                                    Call("logDeriv", Call("value", a), Call("value", h))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The change of variable t = inverse(u)-1 sends (0,1) onto (0,infinity). "
                        + "The absolute Jacobian inverse(u squared) cancels the two inverse-scaling "
                        + "factors. Null endpoints allow replacement of the interval integral by "
                        + "the open-interval integral. The change-of-variables integrability "
                        + "equivalence also proves that the resolvent map is integrable. Evaluation "
                        + "of its continuous-linear-map integral at every Hermitian H agrees with "
                        + "LogDerivTrace.logDeriv(value(A),value(H)), whose matrix inverse convention "
                        + "is connected by nonsing_inv_eq_ringInverse."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "Define entropy(Y) = Re Tr(value(Y) CFC.log(value(Y))); this is trace entropy "
                    + "with the positive sign, rather than the negated von Neumann entropy. "
                    + "entropyHessian(A) denotes fderiv over the reals of fderiv over the reals "
                    + "of entropy at A. gradientMap(C) sends H to Re Tr(value(H) C). "
                    + "The first Hessian argument differentiates the gradient and the second "
                    + "evaluates the resulting linear functional.")),
                Describe.Lean(
                    DescribeId.Create("actual-trace-entropy-bkm-hessian"),
                    DeclarationHandle.Create(Owner + "trace_entropy_hessian_resolvent"),
                    H("The entropy Hessian is the BKM form and is nonnegative on the diagonal"),
                    StatementSource.FromAuthor(Disp(All(parameters,
                        Implies(hypothesis, And(
                            Call("HasFDerivAt", Call("entropyGradient", n),
                                Call("compose", Call("gradientMap", n), resolvent), a),
                            And(All([Bound("H", s), Bound("J", s)],
                                    Eqn(Call("apply", hessian, h, j),
                                        Call("realTraceProduct", Call("value", j),
                                            Call("logDeriv", Call("value", a), Call("value", h))))),
                                All([Bound("H", s)],
                                    Le(D(0), Call("apply", hessian, h, h))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The product rule and trace_mul_logDeriv give the entropy gradient "
                            + "H to Re Tr(value(H)(log(value(A))+I)). This gradient formula holds "
                            + "throughout a common positive neighborhood, so differentiating it "
                            + "identifies the actual fderiv Hessian with the resolvent form. For a "
                            + "Hermitian H, the trace of value(H) R value(H) R is nonnegative "
                            + "when R = inverse(value(A)+tI) is positive semidefinite. Moving "
                            + "trace and multiplication through the integrable Bochner integral "
                            + "proves diagonal nonnegativity.")),
                        Paragraph(Text(
                            "The BKM resolvent form is classical and is recorded in the cited Petz "
                            + "source. The statement here identifies it with the actual derivative "
                            + "of the actual trace-entropy gradient on the full real Hermitian "
                            + "space. It asserts nonnegativity, without asserting strict positivity "
                            + "or extending the differentiation statement to singular matrices."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "Bhatia's Matrix Analysis provides the classical matrix-analysis setting; "
                    + "Petz gives the resolvent BKM form and its logarithmic differential "
                    + "in equations (24), (25), (28), and (29). These references attest the "
                    + "classical formulas. The proofs above establish their CFC and derivative "
                    + "interfaces in the present real Hermitian space. Binary conditional "
                    + "expectation curvature, square contraction, singular-state limits, and "
                    + "sharp contraction coefficients require further arguments.")),
                Reference(LibraryNoteRef.Create("D5/L/Divergence/bhatia1997matrixanalysis")),
                Reference(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
