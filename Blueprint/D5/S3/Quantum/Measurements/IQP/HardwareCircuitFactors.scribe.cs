using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.IQP;

internal sealed class HardwareCircuitFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/lidar2025dadqc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
"HardwareCircuitFactors describes the forced-twin mechanism for QPU-restricted IQP circuits.",
        H("Hardware Circuit Factors"),
        Blocks(
            Node("lidar-connector", "connector", F2(),
                "The displayed expression defines connector. Fin.divNat and Fin.modNat give the quotient and remainder after the product-size cast. Nat.div and Nat.mod denote integer division and remainder; every cast displays its target or equality proof.", "connector",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-hardwareadj", "hardwareAdj", F3(),
                "The displayed expression defines hardwareAdj.", "hardwareAdj",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-h", "H", F4(),
                "The simple hardware graph has the displayed adjacency: each component is K6 without the edge between vertices 4 and 5, and consecutive blocks have the cyclic connector from 5 to 4.", "H",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-hardwareedges", "hardwareEdges", F5(),
                "The displayed expression defines hardwareEdges.", "hardwareEdges",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-edgedegree", "edgeDegree", F7(),
                "The displayed expression defines edgeDegree.", "edgeDegree",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-f4", "F4", F8(),
                "Definition 1, p. 4, verbatim from the source TeX: \"Let \\mH_n=(\\mV_{\\mH},\\mE_{\\mH}) be a fixed simple D-regular hardware graph on n labeled vertices, and let 3\\le d\\le D be a fixed constant (n-independent). The \\emph{d-factors} of a graph \\mH are \\mF_d(\\mH) \\equiv \\{\\mG=(\\mV,\\mE_{\\mG}) : \\mE_{\\mG}\\subseteq \\mE_{\\mH},\\deg_{\\mG}(v)=d\\ \\forall v\\in\\mV\\}. The \\emph{QPU-restricted graph ensemble} is the probability space \\mathrm{Unif}[\\mF_d(\\mH_n)] in which, for each run of \\UDAD, a graph \\mG\\in\\mF_d(\\mH_n) is drawn uniformly at random.\" Here d is four; ordered endpoint pairs record each undirected edge once, and all four-factors are retained.", "F4",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-randomlayer", "randomLayer", F10(),
                "The displayed expression defines randomLayer.", "randomLayer",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-hz", "HZ", F11(),
                "Equation (19) uses the Hamiltonian H prime Z from Eq. (19b): each single-qubit angle is fixed to pi/7, and every selected edge has coupling pi/4. The diagonal entries use the Z eigenvalues of the bit string.", "HZ",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-circuit", "circuit", F13(),
                "Equation (19), verbatim: \\UIQP^{(\\theta)} = U_{\\mathrm{R}}^{(\\theta)} e^{-i H'_Z} W^{\\otimes n}. The definition is this literal matrix product, with randomLayer the tensor product of hadamard times rotation 1 theta_i in Bool coordinates.", "circuit",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-outputprobability", "outputProbability", F14(),
                "The probability is the squared modulus of the literal circuit matrix element from the all-false input to the output s.", "outputProbability",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-uniformangles", "uniformAngles", F15(),
                "The angle distribution is specified on p. 4, verbatim from the source TeX: \"We choose i.i.d. angles \\{\\theta_i\\}_{i=1}^n uniformly from [0,2\\pi),\". The displayed product measure expresses the independence of all coordinates.", "uniformAngles",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-joint", "joint", F16(),
                "The graph and angles are independent; their joint law is the product measure.", "joint",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-tailprobability", "tailProbability", F17(),
                "The displayed expression defines tailProbability.", "tailProbability",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lidar-localedges", "localEdges", F18(),
                "The displayed table defines localEdges : Fin 14 → Fin 6 × Fin 6, the fourteen internal edges of K6 with the edge (4,5) removed.", "localEdges",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-localdegree", "localDegree", F19(),
                "The displayed expression defines localDegree.", "localDegree",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-boundarydegree", "boundaryDegree", F20(),
                "The displayed expression defines boundaryDegree.", "boundaryDegree",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-localmatching", "LocalMatching", F21(),
                "The displayed expression defines LocalMatching.", "LocalMatching",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-blockequiv", "blockEquiv", F22(),
                "The displayed expression defines blockEquiv.", "blockEquiv",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-blockequiv-val", "blockEquiv val", F23(),
                "This statement supplies the indicated blockEquiv val relation for the finite twin-pair calculation.", "blockEquiv_val",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-component-encode", "component encode", F24(),
                "This statement supplies the indicated component encode relation for the finite twin-pair calculation.", "block_encode",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-localneighbours", "localNeighbours", F25(),
                "The displayed expression defines localNeighbours.", "localNeighbours",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-hardware-adj-encoded", "hardware adj encoded", F26(),
                "This statement supplies the indicated hardware adj encoded relation for the finite twin-pair calculation.", "hardware_adj_encoded",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-cyclic-next-val", "cyclic next val", F27(),
                "This statement supplies the indicated cyclic next val relation for the finite twin-pair calculation.", "cyclic_next_val",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-cyclic-prev-iff", "cyclic prev iff", F28(),
                "This statement supplies the indicated cyclic prev iff relation for the finite twin-pair calculation.", "cyclic_prev_iff",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-cyclic-next-iff", "cyclic next iff", F29(),
                "This statement supplies the indicated cyclic next iff relation for the finite twin-pair calculation.", "cyclic_next_iff",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-hardware-adj-encoded-cycle", "hardware adj encoded cycle", F30(),
                "This statement supplies the indicated hardware adj encoded cycle relation for the finite twin-pair calculation.", "hardware_adj_encoded_cycle",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-encoded-neighbours-card", "encoded neighbours card", F31(),
                "This statement supplies the indicated encoded neighbours card relation for the finite twin-pair calculation.", "encoded_neighbours_card",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-orderededge-hardware", "orderedEdge hardware", F33(),
                "This statement supplies the indicated orderedEdge hardware relation for the finite twin-pair calculation.", "orderedEdge_hardware",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-hardware-incident-card", "hardware incident card", F34(),
                "This statement supplies the indicated hardware incident card relation for the finite twin-pair calculation.", "hardware_incident_card",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-hardware-degree-five", "hardware degree five", F35(),
                "For more than one component the hardware is five-regular, as required by Definition 1 with D=5.", "hardware_degree_five",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-factor-complement-matching", "factor complement matching", F36(),
                "This statement supplies the indicated factor complement matching relation for the finite twin-pair calculation.", "factor_complement_matching",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-edgeadj", "edgeAdj", F37(),
                "The displayed expression defines edgeAdj.", "edgeAdj",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-edgeadj-hardware", "edgeAdj hardware", F39(),
                "This statement supplies the indicated edgeAdj hardware relation for the finite twin-pair calculation.", "edgeAdj_hardware",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-edgeadj-symm", "edgeAdj symm", F40(),
                "This statement supplies the indicated edgeAdj symm relation for the finite twin-pair calculation.", "edgeAdj_symm",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-subset-incident-card", "subset incident card", F41(),
                "This statement supplies the indicated subset incident card relation for the finite twin-pair calculation.", "subset_incident_card",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-matching-neighbour-unique", "matching neighbour unique", F42(),
                "This statement supplies the indicated matching neighbour unique relation for the finite twin-pair calculation.", "matching_neighbour_unique",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-localmatchingflags", "localMatchingFlags", F43(),
                "The displayed expression defines localMatchingFlags.", "localMatchingFlags",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-connectorflag", "connectorFlag", F44(),
                "The displayed expression defines connectorFlag.", "connectorFlag",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-subset-degree-local", "subset degree local", F45(),
                "This statement supplies the indicated subset degree local relation for the finite twin-pair calculation.", "subset_degree_local",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-hardware-internal-vertex", "hardware internal vertex", F46(),
                "This statement supplies the indicated hardware internal vertex relation for the finite twin-pair calculation.", "hardware_internal_vertex",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-factor-component-twins", "factor component twins", F47(),
                "Every four-factor contains, in each hardware component, two nonadjacent vertices with the other four component vertices as their exact common neighbourhood. This forces a positive density of twin pairs independently of the choice of factor.", "factor_block_twins",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-angle-integral-eq", "angle integral eq", F48(),
                "The conditional Lebesgue integral is the interval integral divided by the interval length.", "angle_integral_eq",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-angle-integrable-of-continuous", "angle integrable of continuous", F49(),
                "A continuous real function is integrable over the normalized finite angle interval.", "angle_integrable_of_continuous",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-angle-cos-mean", "angle cos mean", F50(),
                "The normalized cosine integral over a full period vanishes.", "angle_cos_mean",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-pairangle", "pairAngle", F51(),
                "The displayed expression defines pairAngle.", "pairAngle",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-paircos", "pairCos", F52(),
                "The displayed expression defines pairCos.", "pairCos",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-fractional-markov", "fractional markov", F53(),
                "This statement supplies the indicated fractional markov relation for the finite twin-pair calculation.", "fractional_markov",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-eventual-tail-bound", "eventual tail bound", F54(),
                "This statement supplies the indicated eventual tail bound relation for the finite twin-pair calculation.", "eventual_tail_bound",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-normalized-periodic-shift", "normalized periodic shift", F55(),
                "This statement supplies the indicated normalized periodic shift relation for the finite twin-pair calculation.", "normalized_periodic_shift",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-conditional-fractional-moment", "conditional fractional moment", F56(),
                "This statement supplies the indicated conditional fractional moment relation for the finite twin-pair calculation.", "conditional_fractional_moment",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-pi-periodic-shift", "pi periodic shift", F57(),
                "A bounded continuous function that is periodic in each coordinate has the same normalized product-angle integral after any fixed coordinate shift. The proof integrates one coordinate at a time.", "pi_periodic_shift",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-sign-product", "sign product", F59(),
                "This statement supplies the indicated sign product relation for the finite twin-pair calculation.", "sign_product",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-twinphase", "twinPhase", F60(),
                "The displayed expression defines twinPhase. The three-element List.foldl starts with the first bit and applies Bool.xor to the remaining bits in order.", "twinPhase",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-twinamplitude", "twinAmplitude", F61(),
                "The displayed expression defines twinAmplitude.", "twinAmplitude",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-twin-density-tensor", "twin density tensor", F62(),
                "The complement phase cancels in the Gram sum. The retained density matrix is the exact product of the four-dimensional pair matrices (I4 + X tensor X)/4. The variable qC is a function of the entire complementary bit configuration, so its type is (Fin m -> Fin 4 -> Bool) -> Bool.", "twin_density_tensor",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-effect-entry", "effect entry", FEffectEntry(),
                "The gate-row projector has the displayed trigonometric entries.", "effect_entry",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("lidar-effect", "effect", F63(),
                "The displayed expression defines effect.", "effect",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-pair-density-entry", "pair density entry", FPairDensityEntry(),
                "The two-qubit density matrix retains exactly equal parity indices.", "pair_density_entry",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("lidar-pairdensity", "pairDensity", F64(),
                "The displayed expression defines pairDensity.", "pairDensity",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lidar-measurement-tensor", "measurement tensor", F65(),
                "This statement supplies the finite product measurement tensor used by the twin marginal calculation.", "measurement_tensor",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-effect-integrable", "effect integrable", F66(),
                "The single-qubit effect is integrable under the normalized angle measure.", "effect_integrable",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lidar-complementary-effect-mean", "complementary effect mean", F67(),
                "The product angle integral of complementary single-qubit effects factors into the corresponding diagonal means.", "complementary_effect_mean",
                DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name)
    {
        var parts = name.Split('.');
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SortedPair(Formula u, Formula v) =>
        Seq(Parenthesized(Seq(Call("Sym2.sortEquiv"), Sp, Seq(Call("s"), Parenthesized(Seq(u, Comma, v))))), Dot, Call("val"));
    private static Formula BoolCoordinate(Formula b) =>
        Parenthesized(Seq(Call("if"), Sp, Parenthesized(b), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0)));

    private static Formula FoldParity(Formula value) => Parenthesized(Seq(Call("List.foldl"), Sp, Call("Bool.xor"), Sp, Parenthesized(Seq(value, Sp, D(0))), Sp, OpenBracket, Parenthesized(Seq(value, Sp, D(1))), Comma, Sp, Parenthesized(Seq(value, Sp, D(2))), Comma, Sp, Parenthesized(Seq(value, Sp, D(3))), CloseBracket));
    private static Formula FinCoordinate(Formula value, string operation) => Seq(Call("val"), Parenthesized(Seq(Parenthesized(Seq(value, Dot, Call("cast"), Sp, Parenthesized(Seq(Call("Nat"), Dot, Seq(Call("mul"), Underscore, Grp(Call("comm"))), Sp, D(6), Sp, Call("m"))))), Dot, Call(operation))));
    private static Formula F2() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("connector"), Sp, Call("u"), Sp, Call("v"), Sp, Iff, Sp, FinCoordinate(Call("u"), "modNat"), Sp, Eq, Sp, D(5), Sp, Land, Sp, FinCoordinate(Call("v"), "modNat"), Sp, Eq, Sp, D(4), Sp, Land, Sp, FinCoordinate(Call("v"), "divNat"), Sp, Eq, Sp, Seq(Call("Nat"), Dot, Call("mod")), Sp, Parenthesized(Seq(FinCoordinate(Call("u"), "divNat"), Sp, Plus, Sp, D(1))), Sp, Call("m")))))))));
    private static Formula F3() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("hardwareAdj"), Sp, Call("u"), Sp, Call("v"), Sp, Iff, Sp, Call("u"), Sp, Neq, Sp, Call("v"), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(FinCoordinate(Call("u"), "divNat"), Sp, Eq, Sp, FinCoordinate(Call("v"), "divNat"), Sp, Land, Sp, Neg, Sp, Parenthesized(Seq(Parenthesized(Seq(FinCoordinate(Call("u"), "modNat"), Sp, Eq, Sp, D(4), Sp, Land, Sp, FinCoordinate(Call("v"), "modNat"), Sp, Eq, Sp, D(5))), Sp, Lor, Sp, Parenthesized(Seq(FinCoordinate(Call("u"), "modNat"), Sp, Eq, Sp, D(5), Sp, Land, Sp, FinCoordinate(Call("v"), "modNat"), Sp, Eq, Sp, D(4))))))), Sp, Lor, Sp, Call("connector"), Sp, Call("u"), Sp, Call("v"), Sp, Lor, Sp, Call("connector"), Sp, Call("v"), Sp, Call("u")))))))))));
    private static Formula F4() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("H"), Sp, Call("m"))), Dot, Call("Adj"), Sp, Eq, Sp, Call("hardwareAdj")))));
    private static Formula F5() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"), Sp, Eq, Sp, Seq(Call("Finset"), Dot, Call("univ"), Dot, Call("filter")), Sp, Call("fun"), Sp, Call("e"), Sp, Mapsto, Sp, Seq(Call("e"), Dot, D(1), Dot, Call("val")), Sp, Lt, Sp, Seq(Call("e"), Dot, D(2), Dot, Call("val")), Sp, Land, Sp, Call("hardwareAdj"), Sp, Seq(Call("e"), Dot, D(1)), Sp, Seq(Call("e"), Dot, D(2))))));
    private static Formula F7() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeDegree"), Sp, Call("G"), Sp, Call("v"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("G"), Dot, Call("filter")), Sp, Call("fun"), Sp, Call("e"), Sp, Mapsto, Sp, Call("v"), Sp, InMacro, Sp, Seq(Call("s"), Parenthesized(Seq(Seq(Call("e"), Dot, D(1)), Comma, Seq(Call("e"), Dot, D(2))))))), Dot, Call("card")))))))));
    private static Formula F8() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Call("F4"), Sp, Call("m"), Sp, Eq, Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"))), Dot, Seq(Call("powerset"), Dot, Call("filter")), Sp, Call("fun"), Sp, Call("G"), Sp, Mapsto, Sp, Forall, Sp, Call("v"), Comma, Sp, Call("edgeDegree"), Sp, Call("G"), Sp, Call("v"), Sp, Eq, Sp, D(4)))));
    private static Formula F10() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(Theta, Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Cdot, Call("m"))))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))))), Comma, Sp, Seq(Call("randomLayer"), Sp, Call("m"), Sp, Theta, Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("tensorOp"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("i"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("hadamard"), Sp, Cdot, Sp, Call("D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation"), Sp, D(1), Sp, Parenthesized(Parenthesized(Seq(Theta, Sp, Call("i")))))))))), Dot, Call("submatrix"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("s"), Sp, Call("i"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Parenthesized(Seq(Call("s"), Sp, Call("i")))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))))), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("z"), Sp, Call("i"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Parenthesized(Seq(Call("z"), Sp, Call("i")))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0)))))))))));
    private static Formula F11() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("z"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, To, Sp, Call("Bool"))))), Comma, Sp, Parenthesized(Seq(Call("HZ"), Sp, Call("G"), Sp, Call("z"), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, Call("i"), Comma, Sp, Parenthesized(Seq(Seq(Call("Real"), Dot, Call("pi")), Sp, Slash, Sp, D(7))), Sp, Cdot, Sp, Seq(Call("D5"), Dot, Call("S3"), Dot, Call("QuantumBounds"), Dot, Call("MerminMeasurementDependence"), Dot, Call("boolSign")), Sp, Parenthesized(Seq(Call("z"), Sp, Call("i"))))), Sp, Plus, Sp, Parenthesized(Seq(Seq(Call("Real"), Dot, Call("pi")), Sp, Slash, Sp, D(4))), Sp, Cdot, Sp, Sum, Sp, Call("e"), Sp, InMacro, Sp, Call("G"), Comma, Sp, Seq(Call("D5"), Dot, Call("S3"), Dot, Call("QuantumBounds"), Dot, Call("MerminMeasurementDependence"), Dot, Call("boolSign")), Sp, Parenthesized(Seq(Call("z"), Sp, Seq(Call("e"), Dot, D(1)))), Sp, Cdot, Sp, Seq(Call("D5"), Dot, Call("S3"), Dot, Call("QuantumBounds"), Dot, Call("MerminMeasurementDependence"), Dot, Call("boolSign")), Sp, Parenthesized(Seq(Call("z"), Sp, Seq(Call("e"), Dot, D(2))))))))))));
    private static Formula F13()
    {
        Formula m = Call("m"), g = Call("G"), z = Call("z"), s = Call("s"), i = Call("i");
        Formula vertices = Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, m)));
        Formula state = Seq(vertices, Sp, To, Sp, Call("Bool"));
        Formula graph = Seq(Call("Finset"), Sp, Parenthesized(Seq(vertices, Sp, Times, Sp, vertices)));
        Formula angles = Seq(vertices, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))));
        Formula exponential = Seq(Call("Complex.exp"), Sp, Parenthesized(Seq(Minus, Call("Complex.I"), Sp, Cdot, Sp,
            Parenthesized(Seq(Call("HZ"), Sp, g, Sp, z, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))));
        Formula diagonal = Parenthesized(Seq(Call("Matrix.diagonal"), Sp, Parenthesized(Seq(Call("fun"), Sp, z, Sp, Mapsto, Sp, exponential))));
        Formula hadamards = Seq(Parenthesized(Seq(Call("tensorOp"), Sp, Parenthesized(Seq(Call("fun"), Sp, Cdot, Sp, Colon, Sp,
            vertices, Sp, Mapsto, Sp, Call("hadamard"))))), Dot, Call("submatrix"), Sp,
            Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(s, Sp, Colon, Sp, state)), Sp, i, Sp, Mapsto, Sp, BoolCoordinate(Seq(s, Sp, i)))), Sp,
            Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(z, Sp, Colon, Sp, state)), Sp, i, Sp, Mapsto, Sp, BoolCoordinate(Seq(z, Sp, i)))));
        Formula equation = Parenthesized(Seq(Call("circuit"), Sp, g, Sp, Theta, Sp, Eq, Sp,
            Call("randomLayer"), Sp, m, Sp, Theta, Sp, Cdot, Sp, diagonal, Sp, Cdot, Sp, hadamards));
        Formula thetaForall = Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Theta, Sp, Colon, Sp, angles)), Comma, Sp, equation));
        Formula graphForall = Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(g, Sp, Colon, Sp, graph)), Comma, Sp, thetaForall));
        return Disp(Seq(Forall, Sp, Parenthesized(Seq(m, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, graphForall));
    }
    private static Formula F14() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Theta, Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("s"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, To, Sp, Call("Bool"))))), Comma, Sp, Parenthesized(Seq(Call("outputProbability"), Sp, Call("G"), Sp, Theta, Sp, Call("s"), Sp, Eq, Sp, Seq(Call("Complex"), Dot, Call("normSq")), Sp, Parenthesized(Seq(Call("circuit"), Sp, Call("G"), Sp, Theta, Sp, Call("s"), Sp, Parenthesized(Seq(Call("fun"), Sp, Cdot, Sp, Mapsto, Sp, Call("false")))))))))))))));
    private static Formula F15() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Call("uniformAngles"), Sp, Call("m"), Sp, Eq, Sp, Seq(Call("Measure"), Dot, Call("pi")), Sp, Call("fun"), Sp, Cdot, Sp, Mapsto, Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))))));
    private static Formula F16() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Call("joint"), Sp, Call("m"), Sp, Eq, Sp, Parenthesized(Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("uniformOn")), Sp, Parenthesized(Seq(Call("val"), Parenthesized(Seq(Call("F4"), Sp, Call("m")))))))), Dot, Call("prod"), Sp, Parenthesized(Seq(Call("uniformAngles"), Sp, Call("m")))))));
    private static Formula F17() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("s"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, To, Sp, Call("Bool"))))), Comma, Sp, Parenthesized(Seq(Call("tailProbability"), Sp, Call("m"), Sp, Call("a"), Sp, Call("s"), Sp, Eq, Sp, Parenthesized(Seq(Call("joint"), Sp, Call("m"))), Dot, Call("real"), Sp, Seq(OpenBrace, Seq(Omega, Sp, Bar, Sp, Call("a"), Sp, Cdot, Sp, new Formula.Power(Parenthesized(new Formula.Power(Parenthesized(Seq(D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Seq(D(6), Sp, Cdot, Sp, Call("m")))), Seq(Minus, D(1))), Sp, Leq, Sp, Call("outputProbability"), Sp, Omega, Dot, D(1), Sp, Omega, Dot, D(2), Sp, Call("s")), CloseBrace)))))))));
    private static Formula F18() => Disp(
        Seq(Call("localEdges"), Sp, Eq, Sp, Bang, Seq(OpenBracket, Seq(Parenthesized(Seq(D(0), Comma, D(1))), Comma, Parenthesized(Seq(D(0), Comma, D(2))), Comma, Parenthesized(Seq(D(0), Comma, D(3))), Comma, Parenthesized(Seq(D(0), Comma, D(4))), Comma, Parenthesized(Seq(D(0), Comma, D(5))), Comma, Parenthesized(Seq(D(1), Comma, D(2))), Comma, Parenthesized(Seq(D(1), Comma, D(3))), Comma, Parenthesized(Seq(D(1), Comma, D(4))), Comma, Parenthesized(Seq(D(1), Comma, D(5))), Comma, Parenthesized(Seq(D(2), Comma, D(3))), Comma, Parenthesized(Seq(D(2), Comma, D(4))), Comma, Parenthesized(Seq(D(2), Comma, D(5))), Comma, Parenthesized(Seq(D(3), Comma, D(4))), Comma, Parenthesized(Seq(D(3), Comma, D(5)))), CloseBracket)));
    private static Formula F19() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("M"), Sp, Colon, Sp, Call("Fin"), Sp, D(1,4), Sp, To, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("localDegree"), Sp, Call("M"), Sp, Call("v"), Sp, Eq, Sp, Sum, Sp, Call("e"), Sp, Colon, Sp, Call("Fin"), Sp, D(1,4), Comma, Sp, Call("if"), Sp, Seq(Call("Bool"), Dot, Call("and")), Sp, Parenthesized(Seq(Call("M"), Sp, Call("e"))), Sp, Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("or")), Sp, Parenthesized(Seq(Call("decide"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("localEdges"), Sp, Call("e"))), Dot, D(1), Sp, Eq, Sp, Call("v"))))), Sp, Parenthesized(Seq(Call("decide"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("localEdges"), Sp, Call("e"))), Dot, D(2), Sp, Eq, Sp, Call("v"))))))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0)))))));
    private static Formula F20() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("incoming"), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("outgoing"), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("boundaryDegree"), Sp, Call("incoming"), Sp, Call("outgoing"), Sp, Call("v"), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, Seq(Call("Bool"), Dot, Call("and")), Sp, Parenthesized(Seq(Call("decide"), Sp, Parenthesized(Seq(Call("v"), Sp, Eq, Sp, D(4))))), Sp, Call("incoming"), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, Seq(Call("Bool"), Dot, Call("and")), Sp, Parenthesized(Seq(Call("decide"), Sp, Parenthesized(Seq(Call("v"), Sp, Eq, Sp, D(5))))), Sp, Call("outgoing"), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0)))))))))));
    private static Formula F21() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("M"), Sp, Colon, Sp, Call("Fin"), Sp, D(1,4), Sp, To, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("incoming"), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("outgoing"), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Call("LocalMatching"), Sp, Call("M"), Sp, Call("incoming"), Sp, Call("outgoing"), Sp, Iff, Sp, Forall, Sp, Call("v"), Comma, Sp, Call("localDegree"), Sp, Call("M"), Sp, Call("v"), Sp, Plus, Sp, Call("boundaryDegree"), Sp, Call("incoming"), Sp, Call("outgoing"), Sp, Call("v"), Sp, Eq, Sp, D(1)))))))));
    private static Formula F22() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Eq, Sp, Seq(Call("finProdFinEquiv"), Dot, Call("trans")), Sp, Parenthesized(Seq(Call("finCongr"), Sp, Parenthesized(Seq(Seq(Call("Nat"), Dot, Seq(Call("mul"), Underscore, Grp(Call("comm")))), Sp, Call("m"), Sp, D(6)))))))));
    private static Formula F23() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("v"))))), Dot, Call("val"), Sp, Eq, Sp, D(6), Sp, Cdot, Sp, Seq(Call("i"), Dot, Call("val")), Sp, Plus, Sp, Seq(Call("v"), Dot, Call("val"))))))))));
    private static Formula F24() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(FinCoordinate(Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("v"))))), "divNat"), Sp, Eq, Sp, Seq(Call("i"), Dot, Call("val")), Sp, Land, Sp, FinCoordinate(Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("v"))))), "modNat"), Sp, Eq, Sp, Seq(Call("v"), Dot, Call("val"))))))))));
    private static Formula F25() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("localNeighbours"), Sp, Call("v"), Sp, Eq, Sp, Seq(Call("Finset"), Dot, Call("univ"), Dot, Call("filter")), Sp, Call("fun"), Sp, Call("w"), Sp, Mapsto, Sp, Call("v"), Sp, Neq, Sp, Call("w"), Sp, Land, Sp, Neg, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("v"), Sp, Eq, Sp, D(4), Sp, Land, Sp, Call("w"), Sp, Eq, Sp, D(5))), Sp, Lor, Sp, Parenthesized(Seq(Call("v"), Sp, Eq, Sp, D(5), Sp, Land, Sp, Call("w"), Sp, Eq, Sp, D(4)))))))));
    private static Formula F26() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("j"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("t"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("hardwareAdj"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("j"), Comma, Call("t"))))), Sp, Iff, Sp, Parenthesized(Seq(Call("i"), Sp, Eq, Sp, Call("j"), Sp, Land, Sp, Call("t"), Sp, InMacro, Sp, Call("localNeighbours"), Sp, Call("r"))), Sp, Lor, Sp, Parenthesized(Seq(Call("r"), Sp, Eq, Sp, D(5), Sp, Land, Sp, Call("t"), Sp, Eq, Sp, D(4), Sp, Land, Sp, Seq(Call("j"), Dot, Call("val")), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("i"), Dot, Call("val")), Sp, Plus, Sp, D(1))), Sp, Call("Nat.mod"), Sp, Call("m"))), Sp, Lor, Sp, Parenthesized(Seq(Call("t"), Sp, Eq, Sp, D(5), Sp, Land, Sp, Call("r"), Sp, Eq, Sp, D(4), Sp, Land, Sp, Seq(Call("i"), Dot, Call("val")), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("j"), Dot, Call("val")), Sp, Plus, Sp, D(1))), Sp, Call("Nat.mod"), Sp, Call("m")))))))))))))));
    private static Formula F27() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("i"), Sp, Plus, Sp, D(1))), Dot, Call("val"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("i"), Dot, Call("val")), Sp, Plus, Sp, D(1))), Sp, Call("Nat.mod"), Sp, Call("m")))))))))));
    private static Formula F28() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("j"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Seq(Call("i"), Dot, Call("val")), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("j"), Dot, Call("val")), Sp, Plus, Sp, D(1))), Sp, Call("Nat.mod"), Sp, Call("m"), Sp, Iff, Sp, Call("j"), Sp, Eq, Sp, Call("i"), Sp, Minus, Sp, D(1)))))))))))));
    private static Formula F29() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("j"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Seq(Call("j"), Dot, Call("val")), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("i"), Dot, Call("val")), Sp, Plus, Sp, D(1))), Sp, Call("Nat.mod"), Sp, Call("m"), Sp, Iff, Sp, Call("j"), Sp, Eq, Sp, Call("i"), Sp, Plus, Sp, D(1)))))))))))));
    private static Formula F30() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("j"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("t"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("hardwareAdj"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("j"), Comma, Call("t"))))), Sp, Iff, Sp, Parenthesized(Seq(Call("i"), Sp, Eq, Sp, Call("j"), Sp, Land, Sp, Call("t"), Sp, InMacro, Sp, Call("localNeighbours"), Sp, Call("r"))), Sp, Lor, Sp, Parenthesized(Seq(Call("r"), Sp, Eq, Sp, D(5), Sp, Land, Sp, Call("t"), Sp, Eq, Sp, D(4), Sp, Land, Sp, Call("j"), Sp, Eq, Sp, Call("i"), Sp, Plus, Sp, D(1))), Sp, Lor, Sp, Parenthesized(Seq(Call("t"), Sp, Eq, Sp, D(5), Sp, Land, Sp, Call("r"), Sp, Eq, Sp, D(4), Sp, Land, Sp, Call("j"), Sp, Eq, Sp, Call("i"), Sp, Minus, Sp, D(1)))))))))))))))))));
    private static Formula F31() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Seq(Call("Finset"), Dot, Call("univ"), Dot, Call("filter")), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("w"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"), Sp, Times, Sp, Call("Fin"), Sp, D(6), Sp, Mapsto, Sp, Call("hardwareAdj"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Call("w"))))))), Dot, Call("card"), Sp, Eq, Sp, D(5)))))))))))));
    private static Formula F33() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("hardwareAdj"), Sp, Call("u"), Sp, Call("v"))), Sp, To, Sp, Parenthesized(Seq(SortedPair(Call("u"), Call("v")), Sp, InMacro, Sp, Call("hardwareEdges"), Sp, Call("m")))))))))));
    private static Formula F34() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeDegree"), Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"))), Sp, Call("v"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("Finset"), Dot, Call("univ"), Dot, Call("filter")), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("w"), Sp, Mapsto, Sp, Call("hardwareAdj"), Sp, Call("v"), Sp, Call("w"))))), Dot, Call("card")))))));
    private static Formula F35() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeDegree"), Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"))), Sp, Call("v"), Sp, Eq, Sp, D(5)))))))))));
    private static Formula F36() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("G"), Sp, InMacro, Sp, Call("F4"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Call("v"), Comma, Sp, Call("edgeDegree"), Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"), Sp, Setminus, Sp, Call("G"))), Sp, Call("v"), Sp, Eq, Sp, D(1)))))))))))));
    private static Formula F37() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeAdj"), Sp, Call("E"), Sp, Call("u"), Sp, Call("v"), Sp, Iff, Sp, SortedPair(Call("u"), Call("v")), Sp, InMacro, Sp, Call("E")))))))))));
    private static Formula F39() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("E"), Sp, Subseteq, Sp, Call("hardwareEdges"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("edgeAdj"), Sp, Call("E"), Sp, Call("u"), Sp, Call("v"))), Sp, To, Sp, Parenthesized(Seq(Call("hardwareAdj"), Sp, Call("u"), Sp, Call("v")))))))))))))));
    private static Formula F40() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("u"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeAdj"), Sp, Call("E"), Sp, Call("u"), Sp, Call("v"), Sp, Iff, Sp, Call("edgeAdj"), Sp, Call("E"), Sp, Call("v"), Sp, Call("u")))))))))));
    private static Formula F41() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("E"), Sp, Subseteq, Sp, Call("hardwareEdges"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Call("edgeDegree"), Sp, Call("E"), Sp, Call("v"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("Finset"), Dot, Call("univ"), Dot, Call("filter")), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("w"), Sp, Mapsto, Sp, Call("edgeAdj"), Sp, Call("E"), Sp, Call("v"), Sp, Call("w"))))), Dot, Call("card")))))))))));
    private static Formula F42() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("G"), Sp, InMacro, Sp, Call("F4"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("v"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))))))), Comma, Sp, Parenthesized(Seq(Exists, Bang, Sp, Call("w"), Comma, Sp, Call("edgeAdj"), Sp, Parenthesized(Seq(Call("hardwareEdges"), Sp, Call("m"), Sp, Setminus, Sp, Call("G"))), Sp, Call("v"), Sp, Call("w")))))))))))))));
    private static Formula F43() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Call("localMatchingFlags"), Sp, Call("E"), Sp, Call("i"), Sp, Eq, Sp, Call("fun"), Sp, Call("e"), Sp, Mapsto, Sp, Call("decide"), Sp, Parenthesized(Seq(Call("edgeAdj"), Sp, Call("E"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Parenthesized(Seq(Call("localEdges"), Sp, Call("e"))), Dot, D(1))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Parenthesized(Seq(Call("localEdges"), Sp, Call("e"))), Dot, D(2)))))))))))))));
    private static Formula F44() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Call("connectorFlag"), Sp, Call("E"), Sp, Call("i"), Sp, Eq, Sp, Call("decide"), Sp, Parenthesized(Seq(Call("edgeAdj"), Sp, Call("E"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, D(5))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Plus, D(1), Comma, D(4)))))))))))))))));
    private static Formula F45() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("E"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("E"), Sp, Subseteq, Sp, Call("hardwareEdges"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Call("edgeDegree"), Sp, Call("E"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Eq, Sp, Call("localDegree"), Sp, Parenthesized(Seq(Call("localMatchingFlags"), Sp, Call("E"), Sp, Call("i"))), Sp, Call("r"), Sp, Plus, Sp, Call("boundaryDegree"), Sp, Parenthesized(Seq(Call("connectorFlag"), Sp, Call("E"), Sp, Parenthesized(Seq(Call("i"), Minus, D(1))))), Sp, Parenthesized(Seq(Call("connectorFlag"), Sp, Call("E"), Sp, Call("i"))), Sp, Call("r")))))))))))))))));
    private static Formula F46() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("j"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("w"), Sp, Colon, Sp, Call("Fin"), Sp, D(6))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Seq(Call("r"), Dot, Call("val")), Sp, Lt, Sp, D(4))), Sp, To, Sp, Parenthesized(Seq(Call("hardwareAdj"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("j"), Comma, Call("w"))))), Sp, Iff, Sp, Call("i"), Sp, Eq, Sp, Call("j"), Sp, Land, Sp, Call("w"), Sp, Neq, Sp, Call("r")))))))))))))))))));
    private static Formula F47() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("NeZero"), Sp, Call("m")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Lt, Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("G"), Sp, Colon, Sp, Call("Finset"), Sp, Parenthesized(Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m"))), Sp, Times, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(6), Sp, Cdot, Sp, Call("m")))))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("G"), Sp, InMacro, Sp, Call("F4"), Sp, Call("m"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("i"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"))), Comma, Sp, Parenthesized(Seq(Exists, Sp, Call("r"), Sp, Call("t"), Sp, Colon, Sp, Call("Fin"), Sp, D(6), Comma, Sp, Call("r"), Sp, Neq, Sp, Call("t"), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Call("j"), Sp, Call("w"), Comma, Sp, Call("edgeAdj"), Sp, Call("G"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("r"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("j"), Comma, Call("w"))))), Sp, Iff, Sp, Call("i"), Sp, Eq, Sp, Call("j"), Sp, Land, Sp, Call("w"), Sp, Neq, Sp, Call("r"), Sp, Land, Sp, Call("w"), Sp, Neq, Sp, Call("t"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Call("j"), Sp, Call("w"), Comma, Sp, Call("edgeAdj"), Sp, Call("G"), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("i"), Comma, Call("t"))))), Sp, Parenthesized(Seq(Call("blockEquiv"), Sp, Call("m"), Sp, Parenthesized(Seq(Call("j"), Comma, Call("w"))))), Sp, Iff, Sp, Call("i"), Sp, Eq, Sp, Call("j"), Sp, Land, Sp, Call("w"), Sp, Neq, Sp, Call("r"), Sp, Land, Sp, Call("w"), Sp, Neq, Sp, Call("t")))))))))))))))));
    private static Formula F48() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, Call("x"), Comma, Sp, Call("f"), Sp, Call("x"), Sp, F.Id("d"), Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))))))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))), Seq(Minus, D(1))), Sp, Cdot, Sp, Int, Sp, Call("x"), Sp, Call("in"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Dot, Dot, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))), Comma, Sp, Call("f"), Sp, Call("x")))));
    private static Formula F49() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Continuous"), Sp, Call("f"))), Sp, To, Sp, Parenthesized(Seq(Call("Integrable"), Sp, Call("f"), Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))))))));
    private static Formula F50() => Disp(
        Seq(Parenthesized(Seq(Int, Sp, Call("x"), Comma, Sp, Seq(Call("Real"), Dot, Call("cos")), Sp, Call("x"), Sp, F.Id("d"), Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))))))), Sp, Eq, Sp, D(0)));
    private static Formula F51() => Disp(
        Seq(Call("pairAngle"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))))), Dot, Call("prod"), Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))));
    private static Formula F52() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Times, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Call("pairCos"), Sp, Call("x"), Sp, Eq, Sp, Seq(Call("Real"), Dot, Call("cos")), Sp, Seq(Call("x"), Dot, D(1)), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("cos")), Sp, Seq(Call("x"), Dot, D(2))))));
    private static Formula F53() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("A"), Sp, Colon, Sp, Call("Type"))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("MeasurableSpace"), Sp, Call("A")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Mu, Sp, Colon, Sp, Call("Measure"), Sp, Call("A"))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("IsProbabilityMeasure"), Sp, Mu), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("Z"), Sp, Colon, Sp, Call("A"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("x"), Comma, Sp, D(0), Sp, Leq, Sp, Call("Z"), Sp, Call("x"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Integrable"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("x"), Sp, Mapsto, Sp, Seq(Call("Real"), Dot, Call("sqrt")), Sp, Parenthesized(Seq(Call("Z"), Sp, Call("x"))))), Sp, Mu)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Int, Sp, Call("x"), Comma, Sp, Seq(Call("Real"), Dot, Call("sqrt")), Sp, Parenthesized(Seq(Call("Z"), Sp, Call("x"))), Sp, F.Id("d"), Mu)), Sp, Leq, Sp, new Formula.Power(Parenthesized(Seq(D(4,7), Sp, Slash, Sp, D(4,8), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Call("m")))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Call("a"))), Sp, To, Sp, Parenthesized(Seq(Mu, Dot, Call("real"), Sp, Seq(OpenBrace, Seq(Call("x"), Sp, Bar, Sp, Call("a"), Sp, Leq, Sp, Call("Z"), Sp, Call("x")), CloseBrace), Sp, Leq, Sp, new Formula.Power(Parenthesized(Seq(Seq(Call("Real"), Dot, Call("sqrt")), Sp, Call("a"))), Seq(Minus, D(1))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(D(4,7), Sp, Slash, Sp, D(4,8), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Call("m"))))))))))))))))))))))))));
    private static Formula F54() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Call("a"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Call("b"))), Sp, To, Sp, Parenthesized(Seq(Exists, Sp, Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, D(3), Sp, Leq, Sp, Call("m"), Sp, Land, Sp, new Formula.Power(Parenthesized(Seq(Seq(Call("Real"), Dot, Call("sqrt")), Sp, Call("a"))), Seq(Minus, D(1))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(D(4,7), Sp, Slash, Sp, D(4,8), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Call("m")), Sp, Lt, Sp, Call("b")))))))))));
    private static Formula F55() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Seq(Call("Function"), Dot, Call("Periodic")), Sp, Call("f"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, Call("x"), Comma, Sp, Call("f"), Sp, Parenthesized(Seq(Call("x"), Sp, Plus, Sp, Call("d"))), Sp, F.Id("d"), Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))))))), Sp, Eq, Sp, Int, Sp, Call("x"), Comma, Sp, Call("f"), Sp, Call("x"), Sp, F.Id("d"), Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))))))))));
    private static Formula F56() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("Y"), Sp, Colon, Sp, Call("Type"))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("MeasurableSpace"), Sp, Call("Y")), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Nu, Sp, Colon, Sp, Call("Measure"), Sp, Call("Y"))), Comma, Sp, Parenthesized(Seq(Seq(OpenBracket, Seq(Call("IsProbabilityMeasure"), Sp, Nu), CloseBracket), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("Z"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("m"), Sp, To, Sp, Parenthesized(Seq(Seq(Mathbb, Grp(F.Id("R"))), Sp, Times, Sp, Seq(Mathbb, Grp(F.Id("R"))))))), Sp, Times, Sp, Call("Y"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("w"), Comma, Sp, D(0), Sp, Leq, Sp, Call("Z"), Sp, Call("w"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("x"), Comma, Sp, Call("Integrable"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("y"), Sp, Mapsto, Sp, Call("Z"), Sp, Parenthesized(Seq(Call("x"), Comma, Sp, Call("y"))))), Sp, Nu, Sp, Land, Sp, Call("Integrable"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("y"), Sp, Mapsto, Sp, Seq(Call("Real"), Dot, Call("sqrt")), Sp, Parenthesized(Seq(Call("Z"), Sp, Parenthesized(Seq(Call("x"), Comma, Sp, Call("y"))))))), Sp, Nu)), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Integrable"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("w"), Sp, Mapsto, Sp, Seq(Call("Real"), Dot, Call("sqrt")), Sp, Parenthesized(Seq(Call("Z"), Sp, Call("w"))))), Sp, Parenthesized(Seq(Parenthesized(Seq(Seq(Call("Measure"), Dot, Call("pi")), Sp, Call("fun"), Sp, Cdot, Sp, Colon, Sp, Call("Fin"), Sp, Call("m"), Sp, Mapsto, Sp, Call("pairAngle"))), Dot, Call("prod"), Sp, Nu)))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("x"), Comma, Sp, Parenthesized(Seq(Int, Sp, Call("y"), Comma, Sp, Call("Z"), Sp, Parenthesized(Seq(Call("x"), Comma, Sp, Call("y"))), Sp, F.Id("d"), Nu)), Sp, Eq, Sp, Prod, Sp, Call("i"), Comma, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Call("pairCos"), Sp, Parenthesized(Seq(Call("x"), Sp, Call("i"))))))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, Call("w"), Comma, Sp, Seq(Call("Real"), Dot, Call("sqrt")), Sp, Parenthesized(Seq(Call("Z"), Sp, Call("w"))), Sp, F.Id("d"), Parenthesized(Seq(Parenthesized(Seq(Seq(Call("Measure"), Dot, Call("pi")), Sp, Call("fun"), Sp, Cdot, Sp, Colon, Sp, Call("Fin"), Sp, Call("m"), Sp, Mapsto, Sp, Call("pairAngle"))), Dot, Call("prod"), Sp, Nu)))), Sp, Leq, Sp, new Formula.Power(Parenthesized(Seq(D(4,7), Sp, Slash, Sp, D(4,8), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Call("m"))))))))))))))))))))))));
    private static Formula F57() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("f"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Continuous"), Sp, Call("f"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("C"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("x"), Comma, Sp, Vert, Call("f"), Sp, Call("x"), Vert, Sp, Leq, Sp, Call("C"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Call("x"), Sp, Call("i"), Comma, Sp, Seq(Call("Function"), Dot, Call("Periodic")), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("t"), Sp, Mapsto, Sp, Call("f"), Sp, Parenthesized(Seq(Seq(Call("Function"), Dot, Call("update")), Sp, Call("x"), Sp, Call("i"), Sp, Call("t"))))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("d"), Sp, Colon, Sp, Call("Fin"), Sp, Call("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, Call("x"), Comma, Sp, Call("f"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("i"), Sp, Mapsto, Sp, Call("x"), Sp, Call("i"), Sp, Plus, Sp, Call("d"), Sp, Call("i"))), Sp, F.Id("d"), Seq(Call("Measure"), Dot, Call("pi")), Sp, Parenthesized(Seq(Call("fun"), Sp, Cdot, Sp, Mapsto, Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi")))))))))))), Sp, Eq, Sp, Int, Sp, Call("x"), Comma, Sp, Call("f"), Sp, Call("x"), Sp, F.Id("d"), Seq(Call("Measure"), Dot, Call("pi")), Sp, Parenthesized(Seq(Call("fun"), Sp, Cdot, Sp, Mapsto, Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp, Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))))))))))))))))))));
    private static Formula NegOne(Formula b) =>
        Seq(Seq(Call("Int"), Dot, Call("negOnePow")), Sp,
            Parenthesized(Seq(Parenthesized(Seq(b, Dot, Call("toNat"))), Sp, Colon, Sp,
                Seq(Mathbb, Grp(F.Id("Z"))))));
    private static Formula F59()
    {
        Formula b = Call("b"), c = Call("c");
        Formula bBinder = Parenthesized(Seq(b, Sp, Colon, Sp, Call("Bool")));
        Formula cBinder = Parenthesized(Seq(c, Sp, Colon, Sp, Call("Bool")));
        Formula xor = Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, b, Sp, c));
        Formula equation = Parenthesized(Seq(NegOne(b), Sp, Times, Sp, NegOne(c), Sp, Eq, Sp, NegOne(xor)));
        Formula body = Parenthesized(Seq(Forall, Sp, cBinder, Comma, Sp, equation));
        return Disp(Seq(Forall, Sp, bBinder, Comma, Sp, body));
    }
    private static Formula F60()
    {
        Formula m = Call("m"), qC = Call("qC"), x = Call("x"), y = Call("y"), i = Call("i");
        Formula mBinder = Parenthesized(Seq(m, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))));
        Formula qType = Parenthesized(Seq(Call("Fin"), Sp, m, Sp, To, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(4), Sp, To, Sp, Call("Bool")))));
        Formula xType = Seq(Call("Fin"), Sp, m, Sp, To, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"));
        Formula yType = Parenthesized(Seq(Call("Fin"), Sp, m, Sp, To, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(4), Sp, To, Sp, Call("Bool")))));
        Formula qBinder = Parenthesized(Seq(qC, Sp, Colon, Sp, qType, Sp, To, Sp, Call("Bool")));
        Formula xBinder = Parenthesized(Seq(x, Sp, Colon, Sp, xType));
        Formula yBinder = Parenthesized(Seq(y, Sp, Colon, Sp, yType));
        Formula xi = Parenthesized(Seq(x, Sp, i)), yi = Parenthesized(Seq(y, Sp, i));
        Formula parity = FoldParity(yi);
        Formula xor = Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, xi, Dot, D(1), Sp, xi, Dot, D(2)));
        Formula phase = Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("and")), Sp, xor, Sp, parity));
        Formula equation = Parenthesized(Seq(Call("twinPhase"), Sp, m, Sp, qC, Sp, x, Sp, y, Sp, Eq, Sp,
            NegOne(Parenthesized(Seq(qC, Sp, y))), Sp, Cdot, Sp, Prod, Sp, i, Comma, Sp, NegOne(phase)));
        Formula yForall = Parenthesized(Seq(Forall, Sp, yBinder, Comma, Sp, equation));
        Formula xForall = Parenthesized(Seq(Forall, Sp, xBinder, Comma, Sp, yForall));
        Formula qForall = Parenthesized(Seq(Forall, Sp, qBinder, Comma, Sp, xForall));
        return Disp(Seq(Forall, Sp, mBinder, Comma, Sp, qForall));
    }
    private static Formula F61() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("qC"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("m"), Sp, To, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(4), Sp, To, Sp, Call("Bool"))))), Sp, To, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("xy"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("m"), Sp, To, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"))), Sp, Times, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("m"), Sp, To, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(4), Sp, To, Sp, Call("Bool"))))))), Comma, Sp, Parenthesized(Seq(Call("twinAmplitude"), Sp, Call("m"), Sp, Call("qC"), Sp, Call("xy"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(new Formula.Power(new Formula.Power(Parenthesized(Seq(D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Seq(Minus, D(1))), Seq(D(3), Sp, Cdot, Sp, Call("m"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Call("twinPhase"), Sp, Call("m"), Sp, Call("qC"), Sp, Seq(Call("xy"), Dot, D(1)), Sp, Seq(Call("xy"), Dot, D(2)), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))));
    private static Formula F62() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("qC"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Call("m"), Sp, To, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(4), Sp, To, Sp, Call("Bool"))))), Sp, To, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("x"), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"), Sp, To, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Seq(Call("x"), Apos), Sp, Colon, Sp, Call("Fin"), Sp, Call("m"), Sp, To, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Call("partialTraceRight"), Sp, Parenthesized(Seq(Seq(Call("Matrix"), Dot, Call("vecMulVec")), Sp, Parenthesized(Seq(Call("twinAmplitude"), Sp, Call("m"), Sp, Call("qC"))), Sp, Parenthesized(Seq(Call("star"), Sp, Parenthesized(Seq(Call("twinAmplitude"), Sp, Call("m"), Sp, Call("qC"))))))), Sp, Call("x"), Sp, Seq(Call("x"), Apos), Sp, Eq, Sp, Prod, Sp, Call("i"), Comma, Sp, Call("if"), Sp, Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, Parenthesized(Seq(Call("x"), Sp, Call("i"))), Dot, D(1), Sp, Parenthesized(Seq(Call("x"), Sp, Call("i"))), Dot, D(2))), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, Parenthesized(Seq(Seq(Call("x"), Apos), Sp, Call("i"))), Dot, D(1), Sp, Parenthesized(Seq(Seq(Call("x"), Apos), Sp, Call("i"))), Dot, D(2))), Sp, Call("then"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(4), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0)))))))))));
    private static Formula F63() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Alpha, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Seq(Call("effect"), Sp, Alpha, Sp, Eq, Sp, Parenthesized(Seq(Call("Matrix.vecMulVec"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("r"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("star"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("hadamard"), Sp, Cdot, Sp, Call("D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation"), Sp, D(1), Sp, Parenthesized(Alpha))), Sp, D(0), Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Call("r")), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))))))))), Sp, Parenthesized(Seq(Call("star"), Sp, Parenthesized(Seq(Call("fun"), Sp, Call("r"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("star"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("hadamard"), Sp, Cdot, Sp, Call("D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.rotation"), Sp, D(1), Sp, Parenthesized(Alpha))), Sp, D(0), Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Call("r")), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))))))))))))))));
    private static Formula FEffectEntry() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Alpha, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("r"), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Seq(Call("r"), Apos), Sp, Colon, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Call("effect"), Sp, Alpha, Sp, Call("r"), Sp, Seq(Call("r"), Apos), Sp, Eq, Sp, Call("if"), Sp, Call("r"), Sp, Eq, Sp, Seq(Call("r"), Apos), Sp, Call("then"), Sp, D(1), Sp, Slash, Sp, D(2), Sp, Call("else"), Sp, Parenthesized(Seq(Parenthesized(Seq(Seq(Call("Real"), Dot, Call("cos")), Sp, Alpha, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Plus, Sp, Parenthesized(Seq(Call("if"), Sp, Call("r"), Sp, Call("then"), Sp, Minus, D(1), Sp, Call("else"), Sp, D(1))), Sp, Cdot, Sp, Seq(Call("Complex"), Dot, Call("I")), Sp, Cdot, Sp, Parenthesized(Seq(Seq(Call("Real"), Dot, Call("sin")), Sp, Alpha, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Slash, Sp, D(2)))))))));
    private static Formula F64() => Disp(
        Seq(Call("pairDensity"), Sp, Eq, Sp, Seq(Parenthesized(Seq(D(1), Sp, Slash, Sp, D(4), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Bool"), Sp, Times, Sp, Call("Bool"))), Sp, Parenthesized(Seq(Call("Bool"), Sp, Times, Sp, Call("Bool"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Plus, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("tensorOp"), Sp, Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(Cdot, Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))))), Sp, Mapsto, Sp, Call("qubitX"))))), Dot, Call("submatrix"), Sp, Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(Call("x"), Sp, Colon, Sp, Parenthesized(Seq(Call("Bool"), Sp, Times, Sp, Call("Bool"))))), Sp, Mapsto, Sp, Bang, OpenBracket, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Seq(Call("x"), Dot, D(1))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))), Comma, Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Seq(Call("x"), Dot, D(2))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))), CloseBracket)), Sp, Parenthesized(Seq(Call("fun"), Sp, Parenthesized(Seq(Call("x"), Sp, Colon, Sp, Parenthesized(Seq(Call("Bool"), Sp, Times, Sp, Call("Bool"))))), Sp, Mapsto, Sp, Bang, OpenBracket, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Seq(Call("x"), Dot, D(1))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))), Comma, Sp, Parenthesized(Seq(Call("if"), Sp, Parenthesized(Seq(Call("x"), Dot, D(2))), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, D(0))), CloseBracket)))))))));
    private static Formula FPairDensityEntry() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(Call("x"), Sp, Colon, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Seq(Call("x"), Apos), Sp, Colon, Sp, Call("Bool"), Sp, Times, Sp, Call("Bool"))), Comma, Sp, Parenthesized(Seq(Call("pairDensity"), Sp, Call("x"), Sp, Seq(Call("x"), Apos), Sp, Eq, Sp, Call("if"), Sp, Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, Seq(Call("x"), Dot, D(1)), Sp, Seq(Call("x"), Dot, D(2)))), Sp, Eq, Sp, Parenthesized(Seq(Seq(Call("Bool"), Dot, Call("xor")), Sp, Seq(Seq(Call("x"), Apos), Dot, D(1)), Sp, Seq(Seq(Call("x"), Apos), Dot, D(2)))), Sp, Call("then"), Sp, D(1), Sp, Slash, Sp, D(4), Sp, Call("else"), Sp, D(0)))))));

    private static Formula F65()
    {
        Formula m = Call("m"), alpha = Call("alpha"), beta = Call("beta"), x = Call("x"), xp = Seq(Call("x"), Apos), i = Call("i");
        Formula mBinder = Parenthesized(Seq(m, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))));
        Formula pairType = Parenthesized(Seq(Call("Fin"), Sp, m, Sp, To, Sp, Parenthesized(Seq(Call("Bool"), Sp, Times, Sp, Call("Bool")))));
        Formula alphaBinder = Parenthesized(Seq(alpha, Sp, Colon, Sp, Call("Fin"), Sp, m, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R")))));
        Formula betaBinder = Parenthesized(Seq(beta, Sp, Colon, Sp, Call("Fin"), Sp, m, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R")))));
        Formula xi = Parenthesized(Seq(x, Sp, i)), xpi = Parenthesized(Seq(xp, Sp, i));
        Formula term = Seq(Call("pairDensity"), Sp, xi, Sp, xpi, Sp, Cdot,
            Sp, Call("effect"), Sp, Parenthesized(Seq(alpha, Sp, i)), Sp, Seq(xi, Dot, D(1)), Sp, Seq(xpi, Dot, D(1)),
            Sp, Cdot, Sp, Call("effect"), Sp, Parenthesized(Seq(beta, Sp, i)), Sp, Seq(xi, Dot, D(2)), Sp, Seq(xpi, Dot, D(2)));
        Formula lhs = Parenthesized(Seq(Sum, Sp, x, Sp, Colon, Sp, pairType, Comma, Sp,
            Sum, Sp, xp, Sp, Colon, Sp, pairType, Comma, Sp, Prod, Sp, i, Comma, Sp, term));
        Formula realNumerator = Seq(D(1), Sp, Plus, Sp, Call("Real.cos"), Sp, Parenthesized(Seq(alpha, Sp, i)), Sp, Cdot, Sp, Call("Real.cos"), Sp, Parenthesized(Seq(beta, Sp, i)));
        Formula realQuotient = Parenthesized(Seq(Parenthesized(realNumerator), Sp, Slash, Sp, D(4), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))));
        Formula rhsTerm = Parenthesized(Seq(realQuotient, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))));
        Formula rhs = Parenthesized(Seq(Prod, Sp, i, Comma, Sp, rhsTerm));
        Formula equation = Parenthesized(Seq(lhs, Sp, Eq, Sp, rhs));
        Formula betaForall = Parenthesized(Seq(Forall, Sp, betaBinder, Comma, Sp, equation));
        Formula alphaForall = Parenthesized(Seq(Forall, Sp, alphaBinder, Comma, Sp, betaForall));
        return Disp(Seq(Forall, Sp, mBinder, Comma, Sp, alphaForall));
    }
    private static Formula F66()
    {
        Formula r = Call("r"), rp = Seq(Call("r"), Apos), alpha = Call("alpha");
        Formula interval = Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp,
            Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))));
        Formula function = Parenthesized(Seq(Call("fun"), Sp, alpha, Sp, Mapsto, Sp, Call("effect"), Sp, alpha, Sp, r, Sp, rp));
        Formula integrable = Parenthesized(Seq(Call("Integrable"), Sp, function, Sp, interval));
        Formula rpForall = Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(rp, Sp, Colon, Sp, Call("Bool"))), Comma, Sp, integrable));
        return Disp(Seq(Forall, Sp, Parenthesized(Seq(r, Sp, Colon, Sp, Call("Bool"))), Comma, Sp, rpForall));
    }
    private static Formula F67()
    {
        Formula k = Call("k"), z = Call("z"), zp = Seq(Call("z"), Apos), alpha = Call("alpha"), i = Call("i");
        Formula kBinder = Parenthesized(Seq(k, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))));
        Formula zType = Seq(Call("Fin"), Sp, k, Sp, To, Sp, Call("Bool"));
        Formula zBinder = Parenthesized(Seq(z, Sp, Colon, Sp, zType));
        Formula zpBinder = Parenthesized(Seq(zp, Sp, Colon, Sp, zType));
        Formula interval = Parenthesized(Seq(Seq(Call("Measure"), Dot, Call("pi")), Sp, Call("fun"), Sp, Cdot, Sp, Colon, Sp,
            Call("Fin"), Sp, k, Sp, Mapsto, Sp, Parenthesized(Seq(Seq(Call("ProbabilityTheory"), Dot, Call("cond")), Sp, Call("volume"), Sp,
                Parenthesized(Seq(Seq(Call("Set"), Dot, Call("Ico")), Sp, D(0), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Seq(Call("Real"), Dot, Call("pi"))))))))));
        Formula effectTerm = Parenthesized(Seq(Call("effect"), Sp, Parenthesized(Seq(alpha, Sp, i)), Sp, Parenthesized(Seq(z, Sp, i)), Sp, Parenthesized(Seq(zp, Sp, i))));
        Formula product = Parenthesized(Seq(Prod, Sp, i, Comma, Sp, effectTerm));
        Formula lhs = Parenthesized(Seq(Int, Sp, alpha, Comma, Sp, product, Sp, F.Id("d"), Sp, interval));
        Formula rhsTerm = Parenthesized(Seq(Call("if"), Sp, Parenthesized(Seq(z, Sp, i, Sp, Eq, Sp, zp, Sp, i)), Sp, Call("then"), Sp,
            Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0)));
        Formula rhs = Parenthesized(Seq(Prod, Sp, i, Comma, Sp, rhsTerm));
        Formula equation = Parenthesized(Seq(lhs, Sp, Eq, Sp, rhs));
        Formula zpForall = Parenthesized(Seq(Forall, Sp, zpBinder, Comma, Sp, equation));
        Formula zForall = Parenthesized(Seq(Forall, Sp, zBinder, Comma, Sp, zpForall));
        return Disp(Seq(Forall, Sp, kBinder, Comma, Sp, zForall));
    }

}
