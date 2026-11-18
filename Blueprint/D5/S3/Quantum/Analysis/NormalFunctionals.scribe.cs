using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class NormalFunctionalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NormalFunctionals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary-directed order-normal continuous complex functionals form a norm-closed complex submodule of the full dual, with its actual restricted Banach norm.",
        H("The normal-functional Banach target"),
        Blocks(
            Node("IsOrderNormal", "Order-normality on directed sets",
                "Let A be any unital complex C-star algebra with a partial order and StarOrderedRing compatibility. For a continuous complex-linear functional phi, IsOrderNormal phi means: for every nonempty upward-directed set s of positive elements, every actual least upper bound a of s, and every real epsilon>0, there is b in s such that ||phi(a-x)||<epsilon for every x in s with b<=x. Positivity is not part of this definition. It includes all directed sets of values, without an external index universe, separability or a sequential restriction.", false),
            Node("normalDual", "The actual complex normal subspace",
                "The carrier consists exactly of continuous functionals satisfying IsOrderNormal. Zero, addition and multiplication by arbitrary complex scalars preserve this predicate. For addition, directedness supplies a common upper tail for the two epsilon/2 witnesses. The norm and complex vector-space structure are inherited from StrongDual C A.", false),
            Node("isClosed_setOf_isOrderNormal", "Closure in dual norm",
                "The set of order-normal functionals is closed in the operator norm. For x in a positive directed set with least upper bound a, one has 0<=a-x<=a and therefore ||a-x||<=||a||. Given a functional phi in the closure and epsilon>0, approximate it by a normal psi within epsilon/(2(||a||+1)). The normal tail of psi at epsilon/2 then controls phi uniformly on that same entire tail. This is a uniform limit argument for arbitrary directed sets, including a=0. The closed-subspace completeness instance normalDual_completeSpace supplies the actual Banach codomain used by NormalL1Realization.exists_normal_L1_extension.", true),
            Node("isOrderNormal_of_domination", "Positive domination preserves normality",
                "If S is order-normal, c is a nonnegative real, and phi is a continuous complex-linear functional satisfying 0<=phi(a)<=c S(a) for every positive a, then phi is order-normal. The statement does not need a separate positivity premise for S. For a positive tail difference, positivity makes phi(a-x) real, and its norm is bounded by c||S(a-x)||. Apply normality of S at epsilon/(c+1). This handles c=0 and the zero algebra without division by c. The lemma is consumed by continuous_normal_of_unit in the entire-L1 realization: 0<=Jg<=||g||J(1) for positive continuous g, followed by the four-positive-part decomposition of any complex g.", true),
            Paragraph(Text("This is the explicit standard order-normal notion for positive functionals on a von Neumann algebra. The source proves completeness of this order-normal functional space; it does not identify it with a Banach space selected by WStarAlgebra.exists_predual, nor prove an ultraweak-continuity equivalence or concrete monotone-operator convergence theorem. No compactness or attainment conclusion is assumed or asserted.")),
            Paragraph(Text("The C-star norm monotonicity and closed-subspace completeness suppliers are reused from pinned Mathlib. The new argument is passage of arbitrary-directed normality through dual-norm limits and its use as a complete target for extension. This is supporting analysis for the unchanged arbitrary-von-Neumann reverse-test attainment problem, which remains open."))
        )));

    private static DocumentBlock Node(string name, string heading, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("normal-functionals-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
