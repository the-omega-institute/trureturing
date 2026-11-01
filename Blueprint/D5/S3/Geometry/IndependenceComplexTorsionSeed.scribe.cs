using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class IndependenceComplexTorsionSeedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/IndependenceComplexTorsionSeed.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit order-two class in the integral finite-chain homology of the eleven-vertex seed.",
        H("The eleven-vertex torsion seed for Question 32"),
        Blocks(
            Paragraph(Text(
                "This is a consumed necessary component in the counterexample route for Carnero Bravo, "
                + "arXiv:2505.06457v2 Question 32, not Question 35 and not another solved original problem. "
                + "No elaboration, kernel check, Scribe build, registration, or publication has run at this "
                + "source-only stage. Project source is pinned at 47c4bf60b02ba7c24acba82e8451ef78dca9ac60; "
                + "Mathlib is pinned at 56a005855ea17e0b0958f73ec801ae140b0a1679.")),
            Paragraph(Text(
                "The exact integers were transcribed from the completed seed-homology.json and "
                + "seed-order-two-certificate.json ordinary mathematical certificates identified in the Lean "
                + "module. They are not trusted Lean assertions. The Lean source supplies finite proofs by "
                + "decide and algebraic proofs, without native_decide, proof placeholders or custom axioms.")),
            Node("actual-seed", "seedComplex", "The project's actual independence complex",
                "H is the graph on Fin 11 decoded from the graph6 payload of JEhbtj{rve?, and G0 is its "
                + "complement. seedComplex is exactly FiniteGraphVertexSubstitution.independenceComplex G0. "
                + "Its eventual realization is FiniteConeCollapse.realization applied to its underlying "
                + "pre-abstract complex.", DescribeRole.Definition),
            Node("edge-basis", "edgeSimplexEquiv", "The complete increasing edge basis",
                "There is a bijection from Fin 32 to the pairs (a,b) with a less than b and {a,b} an actual "
                + "face of seedComplex. The retained edge table supplies the bijection, including its "
                + "injectivity and exhaustiveness. The differential uses this actual simplex enumeration.",
                DescribeRole.Definition),
            Node("triangle-basis", "triangleSimplexEquiv", "The complete increasing triangle basis",
                "There is a bijection from Fin 24 to the triples (a,b,c) with a less than b less than c "
                + "and {a,b,c} an actual face of seedComplex. The retained triangle table supplies this "
                + "bijection, which the triangle boundary uses.", DescribeRole.Definition),
            Node("boundaries-compose", "d1_comp_d2", "The alternating boundaries form a complex",
                "d1.comp d2 = 0. Here C0 = Fin 11 to Z, C1 = Fin 32 to Z and C2 = Fin 24 to Z. "
                + "An oriented edge [a,b] has boundary [b]-[a], and [a,b,c] has boundary "
                + "[b,c]-[a,c]+[a,b]. Finite reduction checks every triangle column; linearity handles "
                + "all integral triangle chains.", DescribeRole.Theorem),
            Node("actual-homology-object", "seedChainComplex", "The finite degree-one homology object",
                "seedChainComplex is ShortComplex.moduleCatMk d2 d1 d1_comp_d2. Its homology is Mathlib's "
                + "ShortComplex.homology in ModuleCat Z. These are all actual degree-zero, degree-one and "
                + "degree-two ordered simplicial chains of seedComplex; higher chains do not change "
                + "ker(d1)/im(d2). No identification with geometric singular homology is assumed.",
                DescribeRole.Definition),
            Node("cycle", "d1_z", "The displayed vector is a cycle",
                "d1 z = 0, where z = [0,3]-[0,7]-[1,3]+[1,5]+[5,7] in the enumerated oriented edge basis.",
                DescribeRole.Theorem),
            Node("double-bounds", "d2_boundingChain", "The retained double bounds integrally",
                "d2 boundingChain = (2 : N) times z. The 24 retained integer coefficients of boundingChain, "
                + "in triangle-table order, are 0,1,1,-1,1,-1,-1,0,-1,-1,1,1,-1,1,-1,1,1,-1,-1,1,0,0,1,1.",
                DescribeRole.Theorem),
            Node("cocycle", "detector_d2", "The extended mod-two cocycle kills all boundaries",
                "For every c : C2, detector (d2 c) = 0. The integer-linear detector to ZMod 2 uses the "
                + "supplied 22 non-tree cocycle values, with zero on the ten retained tree edges. Its "
                + "extension values are proved in the type of extendedCocycle; no spanning-tree "
                + "hypothesis is needed for the non-boundary argument.", DescribeRole.Theorem),
            Node("detected-cycle", "detector_z", "The cocycle detects the cycle",
                "detector z = 1 in ZMod 2.", DescribeRole.Theorem),
            Node("not-boundary", "z_not_boundary", "The cycle is not a boundary",
                "z is not in LinearMap.range d2. If z were d2 c, applying the mod-two detector would "
                + "give one equal to zero.", DescribeRole.Theorem),
            Node("cycle-class", "seedClass", "The displayed class in categorical homology",
                "seedClass : seedChainComplex.homology is cycleClassMap seedChainComplex applied to "
                + "the concrete cycle (z,d1_z). The class map uses the inverse of Mathlib's exact "
                + "moduleCatHomologyIso, so no bespoke quotient comparison is left implicit.",
                DescribeRole.Definition),
            Node("nonzero-killed-two", "seedClass_nonzero_killed_by_two", "Nonzero two-torsion",
                "seedClass is nonzero and (2 : N) times seedClass is zero. This finite-chain torsion "
                + "statement is the intended component consumed by the full Question 32 obstruction.",
                DescribeRole.Theorem),
            Node("exact-order", "seedClass_addOrderOf", "Exact additive order two",
                "addOrderOf seedClass = 2. This follows from the nonzero class killed by the prime two. "
                + "It makes no classification assertion about the other homology classes.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "Still required is an actual comparison isomorphism from seedChainComplex.homology to "
                + "integral singular H1 of TopCat.of of the subtype of "
                + "FiniteConeCollapse.realization seedComplex.toPreAbstractSimplicialComplex. "
                + "The graph S(G,H) singular-suspension result, its 31326 genuine iterations, transport to "
                + "the 93999-vertex induced king graph in the 9337 by 9061 grid, and the torsion-free "
                + "sphere-wedge obstruction are outside this module. No large independence complex is "
                + "enumerated, and no full topology verification or literature novelty is claimed.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
