using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class ArbitraryAlphabetSolovayKitaevDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The registered arbitrary finite inverse-closed dense SU(2) alphabet event is stated with literal ordinary words; the licensed SU(2) algebra and same-word list invariant compile, while the quantitative closure remains open.",
        H("Arbitrary-alphabet ordinary-word Solovay–Kitaev candidate"),
        Blocks(
            Describe.Lean(DescribeId.Create("su2-quaternion"), DeclarationHandle.Create(Prefix + "su2"),
                H("The licensed quaternion matrix"), StatementSource.FromAuthor(Disp(F.Id("su2"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The matrix su2(w,x,y,z) is the unit-quaternion 2 by 2 complex matrix. " +
                    "The source attribution is Csd@9b2d2c17e926ae13795119c5f2f62e85ea240c2d, " +
                    "CsdLean4/Mathlib/QuantumInfo/SU2Rotation.lean (declarations su2, su2_mul, " +
                    "su2_det, axisRot, axisRot_det, su2_star, su2_mem_unitary, and " +
                    "axisRot_mem_unitary), under Apache 2.0; the full " +
                    "license is retained at docs/reports/qmutualinfo/csd-lean4-LICENSE.txt."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("su2-multiplication"), DeclarationHandle.Create(Prefix + "su2_mul"),
                H("Quaternion multiplication"), StatementSource.FromAuthor(Disp(F.Id("su2Mul"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Matrix multiplication is the displayed quaternion product. This is the algebraic " +
                    "support used by the balanced commutator construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("axis-rotation-determinant"), DeclarationHandle.Create(Prefix + "axisRot_det"),
                H("Axis rotations have determinant one"), StatementSource.FromAuthor(Disp(F.Id("axisRotDet"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a real unit axis, every axisRot(a,b,c,theta) has determinant one. " +
                    "No density or word-length assertion is hidden in this algebraic support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compact-finite-net"), DeclarationHandle.Create(Prefix + "compact_exists_finite_net"),
                H("Compactness gives a finite net"), StatementSource.FromAuthor(Disp(F.Id("compactFiniteNet"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "This is the compactness finite-net lemma retained from the licensed CSD " +
                    "CliffordTNet source. A compact set in the closure of D has a finite net drawn " +
                    "from D; it supplies the base compactness step without a quantitative cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su2-carrier-set"), DeclarationHandle.Create(Prefix + "SU2Set"),
                H("The determinant-one unitary subset"), StatementSource.FromAuthor(Disp(F.Id("su2Set"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "SU2Set is the closed subset of 2 by 2 matrices satisfying the SU2 carrier predicate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("su2-closed"), DeclarationHandle.Create(Prefix + "isClosed_SU2Set"),
                H("The SU2 subset is closed"), StatementSource.FromAuthor(Disp(F.Id("isClosedSu2Set"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Closedness uses the existing unitary closed-set theorem and continuity of the matrix determinant."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su2-closed-ball"), DeclarationHandle.Create(Prefix + "su2Set_subset_closedBall"),
                H("The SU2 subset lies in the unit ball"), StatementSource.FromAuthor(Disp(F.Id("su2SetClosedBall"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every unitary has operator norm one, giving the closed-ball bound used by the compactness proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su2-compact"), DeclarationHandle.Create(Prefix + "isCompact_SU2Set"),
                H("The SU2 subset is compact"), StatementSource.FromAuthor(Disp(F.Id("isCompactSu2Set"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The unitary norm bound places SU2Set in the closed unit ball, so closedness yields compactness."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su2-closure-density"), DeclarationHandle.Create(Prefix + "SU2Set_subset_closure_evalGamma"),
                H("Density reaches the compact SU2 carrier"), StatementSource.FromAuthor(Disp(F.Id("su2SetClosureEval"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The density premise is converted into inclusion of SU2Set in the closure of the actual " +
                    "ordinary-word evaluations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-actual-word-net"), DeclarationHandle.Create(Prefix + "exists_finite_word_net"),
                H("A finite actual-word base net with maximum length"), StatementSource.FromAuthor(Disp(F.Id("finiteWordNet"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every positive radius, compactness and density produce a finite Fin(Fin m) word set, " +
                    "a maximum actual List length L0, and an approximation witness for every SU2 target. " +
                    "The theorem records existence only and gives no effectiveness or cardinality bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commutator-quadratic"), DeclarationHandle.Create(Prefix + "norm_mul_sub_mul_comm_le"),
                H("Near-identity commutators are quadratic"), StatementSource.FromAuthor(Disp(F.Id("commutatorQuadratic"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The norm of VW-WV is bounded by twice the product of the two distances to identity. " +
                    "This is the licensed balanced-commutator contraction support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commutator-identity"), DeclarationHandle.Create(Prefix + "groupCommutator_sub_one_eq"),
                H("Unitary commutator factorization"), StatementSource.FromAuthor(Disp(F.Id("commutatorIdentity"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For unitary factors, the group commutator minus identity factors through VW-WV and the " +
                    "trailing adjoint product."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commutator-basic-stability"), DeclarationHandle.Create(Prefix + "norm_groupCommutator_sub_le_basic"),
                H("Basic commutator contraction bound"), StatementSource.FromAuthor(Disp(F.Id("commutatorBasic"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Unitary factors near identity give the standard quadratic group-commutator bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("product-perturbation"), DeclarationHandle.Create(Prefix + "norm_mul_sub_mul_le_weighted"),
                H("Two-factor perturbation estimate"), StatementSource.FromAuthor(Disp(F.Id("productPerturbation"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A product difference is bounded by the two factor differences weighted by the companion norms."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commutator-factor-stability"), DeclarationHandle.Create(Prefix + "norm_mul_sub_mul_comm_sub_le"),
                H("Perturbing both commutator factors"), StatementSource.FromAuthor(Disp(F.Id("commutatorFactorStability"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The difference of two factor commutators is bounded by 4*a*delta when all four factors " +
                    "are within a of identity and each replacement has error at most delta."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commutator-stability"), DeclarationHandle.Create(Prefix + "norm_groupCommutator_sub_le"),
                H("Balanced-commutator stability"), StatementSource.FromAuthor(Disp(F.Id("commutatorStability"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The licensed perturbation estimate bounds the change in a unitary group commutator by " +
                    "4*a*delta*(1+a), the stability shape needed before the 3/2 error recurrence can be closed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su2-carrier"), DeclarationHandle.Create(Prefix + "SU2"),
                H("The determinant-one unitary carrier"), StatementSource.FromAuthor(Disp(F.Id("SU2"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "SU2 U means that U is a unitary 2 by 2 complex matrix and has determinant one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dense-alphabet"), DeclarationHandle.Create(Prefix + "DenseAlphabet"),
                H("Density of actual ordinary words"), StatementSource.FromAuthor(Disp(F.Id("denseAlphabet"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every determinant-one unitary U and every positive eta, some actual List(Fin m) " +
                    "word has L2 operator-norm error strictly less than eta."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polylog-conclusion"), DeclarationHandle.Create(Prefix + "UniformPolylog"),
                H("Uniform polylogarithmic ordinary-word conclusion"), StatementSource.FromAuthor(Disp(F.Id("uniformPolylog"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "UniformPolylog Gamma asks for K>0 and 0<epsilon0<1 and one actual word for each " +
                    "U and 0<epsilon<=epsilon0, satisfying both the error and real length bounds."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residual"), DeclarationHandle.Create(Prefix + "residual"),
                H("Residual from the previous-level word"), StatementSource.FromAuthor(Disp(F.Id("residual"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The residual is U * star(evalGamma u), so the successor construction starts from the " +
                    "previous-level witness u rather than a fixed initial-net word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordinary-word-evaluation"), DeclarationHandle.Create(Prefix + "evalGamma"),
                H("Left-to-right ordinary-word evaluation"), StatementSource.FromAuthor(Disp(F.Id("evalGamma"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For Gamma : Fin m -> Matrix (Fin 2) (Fin 2) Complex, evalGamma [] is the identity " +
                    "and evalGamma (i :: w) is Gamma i multiplied by evalGamma w. The order is literal " +
                    "and is used unchanged by every successor witness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inverse-word"), DeclarationHandle.Create(Prefix + "inverseWord"),
                H("The selector-defined inverse word"), StatementSource.FromAuthor(Disp(F.Id("inverseWord"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "inverseWord inverseLetter w is reverse.map inverseLetter. The selector is not " +
                    "required to be involutive; the compiled inverse evaluation theorem uses only " +
                    "Gamma (inverseLetter i) = star (Gamma i)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inverse-word-length"), DeclarationHandle.Create(Prefix + "inverseWord_length"),
                H("Inverse words preserve actual length"), StatementSource.FromAuthor(Disp(F.Id("inverseWordLength"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Reversing and mapping the selector preserves the exact List length. This is the " +
                    "length used by the produced ordinary witness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-word"), DeclarationHandle.Create(Prefix + "balancedCommutatorWord"),
                H("The literal balanced successor word"), StatementSource.FromAuthor(Disp(F.Id("balancedCommutatorWord"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The successor is exactly v ++ w ++ inv(v) ++ inv(w) ++ u. Its residual is formed " +
                    "from the previous-level u, and the same produced list is used for the value identity " +
                    "and for its length."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balanced-word-length"), DeclarationHandle.Create(Prefix + "successorWord_length"),
                H("The literal successor length"), StatementSource.FromAuthor(Disp(F.Id("successorWordLength"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The same successor list has length length(v)+length(w)+length(v)+length(w)+length(u). " +
                    "No scalar skLength or compressed-word convention is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-word-value"), DeclarationHandle.Create(Prefix + "successorWord_value"),
                H("Evaluation of the same successor witness"), StatementSource.FromAuthor(Disp(F.Id("successorWordValue"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The literal list evaluates to eval(v) * eval(w) * star(eval(v)) * star(eval(w)) * eval(u). " +
                    "This preserves the source's ordinary-list inverse mechanism and does not infer length " +
                    "from a scalar cost function."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("residual-successor-value"), DeclarationHandle.Create(Prefix + "residual_successorWord_value"),
                H("Residual transport through the same successor"), StatementSource.FromAuthor(Disp(F.Id("residualSuccessorValue"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Multiplying the residual U*star(eval(u)) by the produced successor keeps the previous " +
                    "level word u explicit and exposes the balanced commutator factor in one identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("registered-event"), DeclarationHandle.Create(Prefix + "OrdinaryWordSolovayKitaevEvent"),
                H("The exact registered event telescope"), StatementSource.FromAuthor(Disp(F.Id("ordinaryWordSolovayKitaevEvent"))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "For every m, including m = 0, and every finite Gamma : Fin m -> Mat2, assume each " +
                        "letter is unitary, inverse closure holds by an existential selector, and every " +
                        "determinant-one unitary is approximated by an ordinary List(Fin m) in the complex " +
                        "Euclidean L2 operator norm. The conclusion asks for K > 0 and 0 < epsilon0 < 1, " +
                        "uniformly for all U and 0 < epsilon <= epsilon0, with the same word satisfying " +
                        "the error bound and real(length(w)) <= K * (log(1/epsilon))^(log(5)/log(3/2)).")),
                    Paragraph(Text(
                        "The event makes no effectiveness, numerical constant, runtime, optimality, " +
                        "physical implementation, growing-dimension, or compressed-word claim."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitative-closure"), DeclarationHandle.Create(Prefix + "QuantitativeClosure"),
                H("The remaining quantitative bridge"), StatementSource.FromAuthor(Disp(F.Id("quantitativeClosure"))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The candidate records the still-open density-derived finite seed, balanced-commutator " +
                    "stability, and same-word induction obligations. This proposition is not presented as a " +
                    "proof of the registered event and carries no freeze or coverage claim."))),
                DescribeRole.Definition))));
}
