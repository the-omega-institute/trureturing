using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class PinchingGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The subentropy increase under coordinate block pinching is nonnegative and convex.",
        H("Finite sign twirls and entropy gaps"),
        Blocks(
            Describe.Lean(DescribeId.Create("block-sign"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.blockSign"),
                H("Independent block signs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Boolean function on the classical index set chooses a sign −1 or +1 independently for each block."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sign-unitary"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.signUnitary"),
                H("Diagonal sign action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal matrix U_s multiplies every coordinate (x,b) by the sign assigned to x. Both U_s*U_s and U_sU_s* equal the identity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sign-unitary-laws"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.sign_unitary"),
                H("Unitary sign action"), StatementSource.FromAuthor(Disp(SignUnitaryFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite coordinate type X and finite within-block type B with decidable equality, and every sign assignment s : X → Bool, the matrix signUnitary s satisfies signUnitary sᴴ · signUnitary s = 1 and signUnitary s · signUnitary sᴴ = 1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("block-sign-twirl"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.signTwirl"),
                H("Exact block pinching"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assign a sign ±1 independently to each classical block x. The diagonal matrix U_s acts by that sign throughout the block. It is self-adjoint and unitary. For every complex matrix A on X×B, the uniform average of U_s A U_s* over all sign choices is exactly blockPinch(A). The identity does not require positivity or trace normalization.")),
                    Paragraph(Text("For entries in the same block the product of the signs is one. For entries in distinct blocks, flipping the sign of the first block pairs summands with their negatives. This finite involution argument covers empty coordinate spaces as well."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("block-sign-twirl-law"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.signTwirl_eq_blockPinch"),
                H("The sign twirl equals block pinching"), StatementSource.FromAuthor(Disp(SignTwirlFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite coordinate type X and finite within-block type B with decidable equality, and every complex matrix A : Matrix (X×B) (X×B) ℂ, signTwirl A = blockPinch A. Thus the uniform conjugation average over all independent block signs retains exactly the entries whose block indices agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sign-orbit-entropy-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.signOrbitEntropyGap"),
                H("The pointwise entropy defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let q(A,z)=Re⟨z,Az⟩/2. Matrix linearity and the sign-twirl identity give q(blockPinch(A),z)=av_s q(U_s A U_s*,z). Therefore η(q(blockPinch(A),z))−av_s η(q(U_s A U_s*,z)) is exactly the finite entropy Jensen gap of the actual sign orbit. For positive semidefinite A, every orbit readout is nonnegative, so this pointwise defect is nonnegative.")),
                    Paragraph(Text("The common Gaussian representation identifies the integral of this defect with Q(blockPinch(A))−Q(A) on positive trace-one matrices: every sign conjugate has the same subentropy and the same fixed Gaussian baseline. Joint convexity of the scalar Jensen gap therefore proves convexity of the actual subentropy pinching gap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("matrix-subentropy-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.matrix_subentropy_concave"),
                H("Concavity of matrix subentropy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On any finite nonempty matrix coordinate space, matrixSubentropy is concave on positive semidefinite trace-one matrices. The quadratic Gaussian readout is matrix-linear and nonnegative. Pointwise concavity of η, integrability from the Gaussian representation, and cancellation of the common dimension baseline give the inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-pinching-gap-laws"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/PinchingGap.actual_pinching_gap_laws"),
                H("Convexity and nonnegativity of the subentropy gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite nonempty coordinate spaces, the map A↦Q(blockPinch(A))−Q(A) is convex on the positive trace-one state space and is nonnegative there. The statement uses the determinant-integral matrixSubentropy itself. It follows by integrating the pointwise finite Jensen-gap laws and cancelling the common coordinate baseline in the Gaussian representation."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instances(string name, Formula body) => Seq(
        OpenBracket, At(Q("Fintype"), X(name)), CloseBracket, Sp,
        OpenBracket, At(Q("DecidableEq"), X(name)), CloseBracket, Sp, body);
    private static Formula Carriers(Formula body) => All("X", Q("Type"), Instances("X",
        All("B", Q("Type"), Instances("B", body))));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Coordinates() => Product(X("X"), X("B"));
    private static Formula Matrices() => At(Q("Matrix"), Coordinates(), Coordinates(), Seq(Mathbb, Grp(X("C"))));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Mul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SignUnitaryFormula()
    {
        Formula u = Typed(At(Q("signUnitary"), X("s")), Matrices());
        Formula adjoint = At(Q("Matrix", "conjTranspose"), u);
        Formula one = Typed(D(1), Matrices());
        return Carriers(All("s", Parenthesized(new Formula.TypeArrow(X("X"), Q("Bool"))),
            And(Equal(Mul(adjoint, u), one), Equal(Mul(u, adjoint), one))));
    }
    private static Formula SignTwirlFormula() => Carriers(All("A", Matrices(),
        Equal(At(Q("signTwirl"), X("A")),
            At(Q("D5", "S3", "Quantum", "Subentropy", "ClassicalQuantumGram", "blockPinch"), X("A")))));
}
