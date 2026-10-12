using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class BinaryExpectationCurvatureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/BinaryExpectationCurvature.";

    public DocumentDefinition Create()
    {
        Formula p = F.Id("P"), s = F.Id("s"), a = F.Id("A"), k = F.Id("K");
        Formula n = F.Id("n"), h = F.Id("H");
        Formula path = Call("BinaryDefectPath");
        Formula space = Call("HermitianSpace", n);
        Formula profile = Call("quadraticProfile", k, s);
        Formula endpoint = Call("quadraticProfile", k, D(1));
        Formula interval = Call("Icc", D(0), D(1));

        Formula summary = And(
            Le(Call("defect", p, s), Mul(Call("sq", s), Call("defect", p, D(1)))),
            And(Le(D(0), Call("defect", p, s)),
                And(Le(Mul(D(2), Call("defect", p, D(1))), Call("slope", p, D(1))),
                    And(Eqn(Call("defect", p, D(0)), D(0)),
                        Eqn(Call("slope", p, D(0)), D(0))))));

        Formula hessian = All([Bound("H", space)],
            Le(D(0), Call("apply2", Call("traceEntropyHessian", a), h, h)));
        Formula hessianAndProfile = And(hessian, Le(profile, Mul(Call("sq", s), endpoint)));
        Formula entropyContraction = Le(
            Call("quantumRelativeEntropy", Call("path", p, s), Call("reference", p)),
            Mul(Call("sq", s),
                Call("quantumRelativeEntropy", Call("path", p, D(1)), Call("reference", p))));
        Formula summaryStatement = All(
            [Bound("P", path), Bound("s", F.Id("Real"))],
            Implies(MemberOf(s, interval), summary));
        Formula hessianStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space),
                Bound("K", Call("CurvatureKernel")), Bound("s", F.Id("Real"))],
            Implies(Call("PosDef", Call("value", a)),
                Implies(MemberOf(s, interval), hessianAndProfile)));
        Formula entropyStatement = All(
            [Bound("n", F.Id("FiniteType")), Bound("A", space),
                Bound("P", Call("QuantumBinaryDefectPath", n)),
                Bound("s", F.Id("Real"))],
            Implies(Call("PosDef", Call("value", a)),
                Implies(MemberOf(s, interval), And(hessian, entropyContraction))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Binary conditional-expectation curvature has an exact square contraction and a nonnegative BKM Hessian.",
            H("Binary Expectation Curvature"),
            Blocks(
                Paragraph(Text(
                    "A CurvatureKernel is a continuous nonnegative real kernel monotone on [0,1]. "
                    + "weightedCurvature integrates (1-r) times the kernel at v r, and "
                    + "quadraticProfile multiplies this integral by v squared. A BinaryDefectPath "
                    + "records a defect, its endpoint slope, and the explicit curvature representation. "
                    + "The matrix layer supplies the BKM Hessian certificate; the square contraction "
                    + "is derived here from monotonicity of the weighted profile.")),
                Describe.Lean(
                    DescribeId.Create("binary-curvature-summary"),
                    DeclarationHandle.Create(Owner + "binary_curvature_summary"),
                    H("The binary defect contracts quadratically and has the stated endpoint bounds"),
                    StatementSource.FromAuthor(Disp(summaryStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "The weighted kernel is monotone because both the kernel argument and the "
                        + "factor 1-r preserve order on the integration interval. Nonnegativity of "
                        + "the kernel gives nonnegativity of the profile. The endpoint slope identity "
                        + "and its nonnegative remainder give the lower bound."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("matrix-hessian-binary-profile-contraction"),
                    DeclarationHandle.Create(Owner + "matrix_hessian_with_binary_profile_contraction"),
                    H("The matrix BKM Hessian and the binary profile contraction hold together"),
                    StatementSource.FromAuthor(Disp(hessianStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "The Hessian conjunct is the diagonal nonnegativity supplied by the actual "
                        + "matrix logarithm resolvent theorem. The second conjunct is the new one-dimensional "
                        + "square contraction for the supplied curvature kernel."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("quantum-relative-entropy-binary-contraction-with-hessian"),
                    DeclarationHandle.Create(Owner + "quantum_relative_entropy_square_contraction_with_hessian"),
                    H("Quantum relative entropy contracts quadratically along the supplied binary path"),
                    StatementSource.FromAuthor(Disp(entropyStatement)),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "The path defect is identified with the repository's finite-dimensional "
                        + "quantum relative entropy. Substituting that identification into the "
                        + "curvature-profile contraction yields the entropy inequality, while the "
                        + "same resolvent certificate supplies Hessian nonnegativity."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The BKM Hessian and logarithmic resolvent ingredients are the classical matrix "
                    + "analysis input recorded by the MatrixLogResolventDerivative source. The exact "
                    + "binary s-squared profile and the combined path statements are repository-derived.")))));
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

    private static Formula MemberOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
