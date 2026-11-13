using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class AcyclicCarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/AcyclicCarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homotopies carried by basis-indexed acyclic subcomplexes.",
        H("The augmented acyclic carrier theorem"), Blocks(
            Paragraph(Text("This is a coefficient and interface port of the carried homotopy mechanism in AxiomMath/TernaryPoly at immutable revision 28679d7cad438a91a732422d4ab1b184ae17e532, Carriers.lean and Cells.lean. The source attribution is Formalized by Claude Sonnet 5.5. The complete Apache 2.0 license and copyright notice are retained in the Lean source. Ordinary module bases replace rational equivariant cell bases; finite support, rather than a finite basis, controls the boundary extension. This formalizes a known general theorem and makes no novelty claim.")),
            Node("carriers", "CarrierData", "Basis-indexed carriers",
                "For an arbitrary commutative ring R, nonnegative ModuleCat chain complexes C and D, an arbitrary family of index types I(n), and bases B(n) of C(n), a carrier assigns submodules A(n,b)(m) of D(m). The target differential preserves each carrier. If c has nonzero coefficient in the basis expansion of the boundary of b, every degree of the carrier of c lies in the corresponding degree of the carrier of b.", DescribeRole.Definition),
            Node("carried", "CarrierData.Carried", "Carried linear maps",
                "A map from C(n) to D(m) is carried when the image of every basis vector b belongs to A(n,b)(m).", DescribeRole.Definition),
            Node("acyclic", "CarrierData.Acyclic", "Augmented carrier acyclicity",
                "The augmentation may take values in an arbitrary R-module. It vanishes on boundaries. In each individual carrier, augmentation-zero elements in degree zero lift to degree one, and cycles in every positive degree lift to the next degree. No contraction or chosen lift is assumed.", DescribeRole.Definition),
            Node("boundary-support", "CarrierData.Carried.face", "Finite-support boundary extension",
                "A carried linear map sends the boundary of each source basis vector into the carrier of that vector. Expand the boundary using Basis.repr, sum only over its finite support, apply coefficient-support nesting to each term, and use closure of the target submodule under scalar multiplication and finite sums.", DescribeRole.Theorem),
            Node("subtraction", "CarrierData.Carried.sub", "Subtraction preserves bounds",
                "The difference of two maps carried in the same degrees remains carried. This helper is consumed by the primitive construction in the homotopy induction.", DescribeRole.Theorem),
            Node("basis-lift", "basis_exists_lift", "Support-preserving basis lift",
                "For any target linear map phi and basis-indexed source map Phi, if every Phi(B(b)) has a preimage in its specified submodule, choose those preimages and extend along the source basis. The extension is carried and its composite with phi equals Phi by basis extensionality. The basis can be empty or infinite, and neither target has a basis requirement.", DescribeRole.Theorem),
            Node("positive-primitive", "CarrierData.exists_carried_primitive", "Positive-degree primitive",
                "A carried map into positive-degree cycles lifts through the target differential with the same individual carrier bounds. The proof consumes basis_exists_lift and the positive-degree acyclicity of each carrier.", DescribeRole.Theorem),
            Node("zero-primitive", "CarrierData.exists_carried_primitive0", "Augmentation-zero primitive",
                "A carried degree-zero map annihilated by the augmentation lifts to degree one with the same carrier bounds. The proof consumes basis_exists_lift and degree-zero augmented acyclicity.", DescribeRole.Theorem),
            Node("integer-scaling", "CarrierData.Carried.comp_left", "Integer scaling preserves bounds",
                "Integer multiples of carried maps remain carried. This helper is consumed by the signed component induction inherited from the source mechanism.", DescribeRole.Theorem),
            Node("boundary-precomposition", "CarrierData.Carried.d_comp", "Boundary precomposition",
                "Precomposing a carried map with the source boundary preserves the shifted carrier bound. This consumes the finite-support boundary extension.", DescribeRole.Theorem),
            Node("sequence", "exists_sequence", "Dependent sequence of primitive choices",
                "Given an initial state and an allowed successor for every state in every degree, dependent recursion produces a sequence satisfying the initial and successor predicates. This source-ported helper is consumed by the carried homotopy induction.", DescribeRole.Theorem),
            Node("component-induction", "CarrierData.exists_carried_homotopy", "Carried component induction",
                "For an arbitrary integer sign and two carried component families obeying the corresponding twisted chain equations and equal augmentation, degree induction constructs carried homotopy components. The state includes the residual cycle condition. Degree zero uses an augmentation-zero primitive; each successor subtracts the preceding homotopy on the source boundary, verifies that the residual is a cycle using the chain equations, and chooses a carrier primitive.", DescribeRole.Theorem),
            Node("native-homotopy", "exists_homotopy", "Native carried chain homotopy",
                "For every commutative ring R, arbitrary nonnegative ModuleCat chain complexes C and D, and arbitrary bases B(n) indexed by I(n), assume differential-closed basis-indexed carriers, nesting for every nonzero coefficient of each source basis boundary, and augmented acyclicity separately in every carrier. For every pair of chain maps f and g that agree after the augmentation D(0) to R and carry B(n)(b) into A(n,b)(n), there exists a native Homotopy f g whose component H.hom n (n+1) sends B(n)(b) into A(n,b)(n+1). The ring, module and index universes are arbitrary. The theorem permits zero rings, empty and infinite source bases, and non-surjective augmentations, and imposes no target basis, target projectivity, source acyclicity, global contractibility or homotopy-as-input hypothesis. The native Homotopy equations give f(0)-g(0)=dH(0), and f(n+1)-g(n+1)=dH(n+1)+H(n)d in positive degrees. The ordinary telescope directly instantiates the signed source core with sign one and builds the native Homotopy with exactly these carrier bounds.", DescribeRole.Theorem),
            Paragraph(Text("The port is retired in favor of direct upstream use when this repository's pinned Mathlib provides an equivalent full theorem, including the basis-local carrier bounds. Upstream acceptance alone is not this condition.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
