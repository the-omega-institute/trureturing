using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class BinaryExpectationCurvatureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/BinaryExpectationCurvature.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), v = F.Id("V"), a = F.Id("A"), h = F.Id("H");
        Formula s = F.Id("s"), rho = F.Id("rho");
        Formula space = Call("HermitianSpace", n), interval = Call("Icc", D(0), D(1));
        Formula plus = Call("add", a, h), minus = Call("sub", a, h);
        Formula path = Call("add", a, Call("smul", s, h));
        Formula symmetry = And(Call("fixedByConjugation", v, a), Call("negatedByConjugation", v, h));
        Formula endpoints = And(Call("PSD", a), And(Call("PSD", plus), Call("PSD", minus)));
        Formula defect = Call("D", plus, a);
        Formula contraction = Le(Call("D", path, a), Mul(Call("sq", s), defect));
        Formula slope = Le(Mul(D(2), defect), Call("realTraceProduct", h, Call("matrixLog", plus)));
        Formula sigma = Call("binaryExpectation", v, rho);
        Formula output = Call("add", Call("smul", s, rho), Call("smul", Call("sub", D(1), s), sigma));
        Formula actualBounds = And(
            Le(Call("D", output, sigma), Mul(Call("sq", s), Call("D", rho, sigma))),
            Implies(Call("PosDef", rho), Le(Mul(D(2), Call("D", rho, sigma)),
                Call("realTraceProduct", Call("sub", rho, sigma), Call("matrixLog", rho)))));
        Formula.BoundVariable[] pathParams = [Bound("n", F.Id("FiniteType")),
            Bound("V", Call("UnitaryMatrices", n)), Bound("A", space), Bound("H", space)];

        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual binary conditional-expectation entropy satisfies a square upper bound and an endpoint derivative bound.",
            H("Binary Conditional-Expectation Entropy Bounds"),
            Blocks(
                Paragraph(Text(
                    "Let n be any finite index type with decidable equality. Matrices are complex, "
                    + "HermitianSpace(n) is their real self-adjoint subspace, and all matrix expressions "
                    + "use the inclusion of this subspace. PSD and PosDef refer to the Loewner order. "
                    + "D(B,A) = Re Tr(B(CFC.log(B)-CFC.log(A))) uses the actual CFC logarithm. "
                    + "No trace normalization or nonempty-index hypothesis is required. "
                    + "Conjugation by a unitary V fixes A and negates H in the first two statements.")),
                Describe.Lean(
                    DescribeId.Create("binary-entropy-square-contraction"),
                    DeclarationHandle.Create(Owner + "binary_entropy_square_contraction"),
                    H("The binary defect contracts by the squared scale, including singular endpoints"),
                    StatementSource.FromAuthor(Disp(All([.. pathParams, Bound("s", F.Id("Real"))],
                        Implies(symmetry, Implies(endpoints, Implies(MemberOf(s, interval), contraction)))))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "Unitary covariance of the CFC logarithm and trace cyclicity make the two "
                        + "entropy paths A+sH and A-sH equal. The mixed pairing Tr(H log(A)) vanishes. "
                        + "The symmetric semidefinite entropy-gap estimate therefore becomes the stated "
                        + "relative-entropy defect bound."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-endpoint-derivative-lower-bound"),
                    DeclarationHandle.Create(Owner + "binary_endpoint_derivative_lower_bound"),
                    H("A positive-definite endpoint has entropy-production pairing at least twice its defect"),
                    StatementSource.FromAuthor(Disp(All(pathParams,
                        Implies(symmetry, Implies(And(Call("PSD", a),
                            And(Call("PosDef", plus), Call("PSD", minus))), slope))))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "For f(t)=entropy(A+tH)-entropy(A), the square estimate gives f(t)<=t squared f(1). "
                        + "The left slope at one is at least 2f(1). The actual entropy differential "
                        + "and the zero trace of H identify that derivative with Re Tr(H log(A+H))."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "For a self-adjoint unitary V, binaryExpectation(V,rho) denotes "
                    + "sigma=(rho+V rho V*)/2, and output=s rho+(1-s)sigma. "
                    + "The self-adjointness of V is required here, while the preceding two "
                    + "statements only require their explicit conjugation symmetries.")),
                Describe.Lean(
                    DescribeId.Create("binary-expectation-entropy-bounds"),
                    DeclarationHandle.Create(Owner + "binary_expectation_entropy_bounds"),
                    H("The actual binary expectation satisfies both bounds"),
                    StatementSource.FromAuthor(Disp(All([Bound("n", F.Id("FiniteType")),
                        Bound("V", Call("UnitaryMatrices", n)), Bound("rho", space), Bound("s", F.Id("Real"))],
                        Implies(Call("SelfAdjoint", v), Implies(Call("PSD", rho),
                            Implies(MemberOf(s, interval), actualBounds)))))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/petz2001bkm")),
                    Blocks(Paragraph(Text(
                        "Set A=sigma and H=rho-sigma. Conjugation by V fixes A and negates H; "
                        + "A+H=rho and A-H=V rho V* are positive semidefinite. These identities "
                        + "supply the hypotheses of the path bounds. The derivative inequality is "
                        + "conditional on positive definiteness of rho, and the contraction allows "
                        + "every positive semidefinite rho and both scale endpoints."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The index type can be a joint system and finite memory space, so the bound "
                    + "has no dimension-dependent coefficient. The proof uses the symmetric "
                    + "finite-amplitude logarithmic remainder rather than an abstract curvature-profile hypothesis. "
                    + "The BKM differential is classical; the cited source supplies that ingredient. "
                    + "The inequalities do not assert that s squared is the best possible coefficient.")))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula MemberOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
