using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class C129QubitBargmannDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered qubit Bargmann trace is the Bloch scalar-plus-oriented-volume formula.",
        H("C129 qubit three-label orientation"), Blocks(
            Definition("c129-qubit-pauli-combination", "Pauli combination", "pauliCombination",
                "The explicit two by two complex matrix with the three real coordinates in the Pauli X, Y and Z slots."),
            Definition("c129-qubit-projector", "Bloch projector expression", "qubitProjector",
                "The affine half-sum of the identity matrix and the Pauli combination. Unit Bloch vectors give the pure-qubit projector case."),
            Definition("c129-qubit-triple-bargmann", "Ordered triple trace", "tripleBargmann",
                "The trace of the ordered product of the three Bloch projector expressions."),
            Definition("c129-qubit-state-projector", "Rank-one state projector", "stateProjector",
                "The rank-one density matrix built from a two-component complex amplitude vector."),
            Definition("c129-qubit-vzero", "Computational basis state", "vZero",
                "The amplitude vector for the state |0⟩."),
            Definition("c129-qubit-vplus", "Real equatorial state", "vPlus",
                "The amplitude vector (|0⟩+|1⟩)/√2."),
            Definition("c129-qubit-vyplus", "Positive Y state", "vYPlus",
                "The amplitude vector (|0⟩+i|1⟩)/√2."),
            Definition("c129-qubit-vyminus", "Negative Y state", "vYMinus",
                "The amplitude vector (|0⟩−i|1⟩)/√2."),
            Definition("c129-qubit-state-triple-bargmann", "State triple trace", "stateTripleBargmann",
                "The trace of the ordered product of three rank-one state projectors."),
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-triple-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch"),
                H("Bloch formula for the ordered qubit trace"),
                StatementSource.FromAuthor(Disp(TripleFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity is proved by expanding the three explicit two by two matrices. It is stated for arbitrary real three-coordinate vectors; unit-norm vectors give the pure-qubit interpretation from the source atom. The scalar terms are the three pairwise dot products and the imaginary term is the oriented scalar triple product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-explicit-bloch"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation"),
                H("Opposite Bloch orientations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered coordinate triples (0,0,1), (1,0,0), and (0,±1,0) give the two values (1+i)/4 and (1-i)/4. The pairwise dot products vanish while the oriented triple product changes sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c129-qubit-bargmann-explicit-states"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation"),
                H("Explicit pure-state witnesses"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For v₁=|0⟩, v₂=(|0⟩+|1⟩)/√2, and v₃±=(|0⟩±i|1⟩)/√2, the rank-one density matrices have ordered traces (1±i)/4. This records the concrete two-sign witness; the remaining geometric interpretation of zero added orthogonal remainder stays in the source prose."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application: an unordered pair comparison loses a cyclic direction"), Blocks(
                Paragraph(Text(
                    "Use precisely the normalized vectors v₁=vZero, v₂=vPlus, v₃⁺=vYPlus and v₃⁻=vYMinus above, with the label order (1,2,3) fixed. Write Pⱼ=|vⱼ⟩⟨vⱼ| and Tᵢⱼ=Tr(PᵢPⱼ)=|⟨vᵢ|vⱼ⟩|². For either sign the full table has diagonal 1 and every off-diagonal entry 1/2: T=[[1,1/2,1/2],[1/2,1,1/2],[1/2,1/2,1]]. Each triple consists of three distinct rays, and the two choices of the third ray are distinct. Thus every pair is comparable, with Tᵢⱼ=Tⱼᵢ; reversing the arguments of this comparison changes no result.")),
                Paragraph(Text(
                    "The existing explicit_state_orientation theorem gives B⁺=Tr(P₁P₂P₃⁺)=(1+i)/4 and B⁻=(1−i)/4. If a function of T alone recovered the ordered B on both triples, the identical argument T would have two different outputs, a contradiction. This excludes recovery by any postprocessing of that table, including a random procedure whose output law depends only on T. It does not say that arbitrary quantum protocols on the actual input states have identical statistics. The observation has discarded information; further arithmetic on it cannot restore that information."))
            )),
            new DocumentBlock.Section(H("Conditional cycle readout and its supplied resources"), Blocks(
                Paragraph(Text(
                    "Assume three separately prepared, stored qubits with the joint product promise R=P₁⊗P₂⊗P₃; for pure inputs put V=v₁⊗v₂⊗v₃. Also supply a control qubit initially |0⟩, coherent controlled permutation access, a calibrated phase between its two branches, and the usual quantum state, unitary-operation and Born measurement rules. Define C|a,b,c⟩=|b,c,a⟩, so (CV)(a,b,c)=V(c,a,b). This direction gives ⟨V|C|V⟩=B, not its conjugate. The three input vectors need no common global-phase locking: their independent scalar phases multiply V by one overall phase and cancel from every density matrix and B.")),
                Paragraph(Text(
                    "Let q have modulus one. Apply a Hadamard to the control, then the controlled C with relative branch factor q, then a second Hadamard, and measure the control in the computational basis. The middle operation is diag(I,qC); its phase is relative to the unchanged control-0 branch. The output is |0⟩⊗K₀V+|1⟩⊗K₁V, where K₀=(I+qC)/2 and K₁=(I−qC)/2. These are actual data-system Kraus operators, not a definition of a scalar called probability. Since C†C=I and q̄q=1, K₀†K₀+K₁†K₁=I. Consequently R↦KₐRKₐ† is a normalized two-outcome finite instrument, with one Kraus operator per outcome.")),
                Paragraph(Text(
                    "The parameter correspondence to finite_kraus_instrument_born_marginal is: n=Fin 2×(Fin 2×Fin 2), Setting=Unit, Outcome=Fin 2, Kraus=Unit, instrumentKraus((),a,())=Kₐ, and rho=R as a DensityState. PureStateHandshake.rankOneDensity supplies R=|V⟩⟨V|, with V normalized; positivity and trace one put it in the existing DensityState carrier. The theorem identifies the branch trace with FiniteDimensional.bornProbability(R,Eₐ), where Eₐ=Kₐ†Kₐ. Thus the operation uses the repository's existing Born/instrument semantics. It does not introduce a new measurement postulate or a new Lean declaration.")),
                Paragraph(Text(
                    "For either of these product inputs, expanding E₀ gives [2I+qC+q̄C†]/4, with E₁=I−E₀. Taking its Born trace against R, using Tr(R)=1 and Tr(RC)=B, gives p₀=(1+Re(qB))/2 and p₁=(1−Re(qB))/2. In particular q=1 reads Re B. With the declared left-cycle direction, q=−i reads Im B: the branch phase gate is diag(1,−i). Reversing C conjugates B and reverses this imaginary-part sign; q=+i with the present C instead gives p₀=(1−Im B)/2. A permutation symbol alone, without its action on tensor factors and its phase convention, is insufficient to fix that sign.")),
                Paragraph(Text(
                    "For the two explicit inputs, q=1 gives (p₀,p₁)=(5/8,3/8) for both. With the same calibrated q=−i device, the plus triple gives (5/8,3/8) and the minus triple gives (3/8,5/8). These are different Bernoulli laws despite the identical pair table. They allow statistical discrimination through repeated independent preparations and readouts. Both outcomes have positive probability under either input, so a decision based on this one binary result cannot identify the sign perfectly. The phase-sensitive apparatus accesses a joint cyclic relation that is absent from T. Preparing a product, preserving the registers, and coherently interfering the branches are additional resources, not consequences of knowing T."))
            )),
            new DocumentBlock.Section(H("Geometry, reference transformations and limits"), Blocks(
                Paragraph(Text(
                    "The Bloch vectors are r₁=(0,0,1), r₂=(1,0,0), r₃±=(0,±1,0). Their pair dot products vanish, while r₁·(r₂×r₃±)=±1. The existing Bloch formula therefore makes Im B one quarter of this oriented volume. Here B is nonzero, so its argument is defined. Relating that phase to an oriented spherical geodesic triangle requires a declared path and geometric-phase sign convention; it does not identify Bloch orientation with spatial chirality. In particular the source volume uses −arg B for its specified geometric-phase convention.")),
                Paragraph(Text(
                    "Independent rephasing of the input vectors leaves B invariant, and a common unitary change of basis preserves its trace-product value. Common complex conjugation sends B to its conjugate. Conjugating the inputs alone while keeping the calibrated q=−i apparatus fixed exchanges the two displayed output laws. Conjugating the entire experiment, including the phase reference q, instead conjugates qB and preserves its real part and all these probabilities. A nonreal B rules out making this entire tuple simultaneously real while preserving that invariant. It does not rule out every real simulation with enlarged state space or extra encoding.")),
                Paragraph(Text(
                    "The application is the known three-state Bargmann cycle test specialized to this owner's qubit witnesses, not a literature novelty. Oszmaniec, Brod and Galvão, Measuring relational information between quantum states, and applications, arXiv:2109.10006v1, equation (1), Figure 1 and the qubit example on PDF pages 1–3 provide the primary reference; Library/HilbertOperators/oszmaniec2021relational.md records the version and convention boundaries. The many-body exchange character readout and the renewal-instrument posterior cycle are different inputs and protocols. No claim here reconstructs arbitrary complex Gram data from pair intensities, resolves every zero-edge overlap network with triangles, derives Born or Lüders rules, selects a complex field from raw kernel positivity, or completes quantum origins.")),
                Paragraph(Text(
                    "In plain terms, every pair in either triple can be compared, and reversing the two endpoints leaves its strength unchanged; the two comparison tables are identical. Yet following the three states around a cycle in a chosen direction can retain an oriented phase absent from the table. If we are additionally supplied with three independently prepared quantum states whose joint state is promised to be a product, storage, a control qubit, a coherent controlled cyclic permutation, a fixed calibrated relative phase reference between the control branches, and Born readout rules, this direction can produce different measurement frequencies. With the declared left cycle and q=−i, the same apparatus gives outcome zero with probability 5/8 for the plus triple and 3/8 for the minus triple. Repeated independent preparations and readouts can distinguish their statistics, but a single readout does not identify the triple perfectly. The pair strengths omit this three-state relation, and the readout needs the stated resources. Pairwise comparability alone derives neither these operations nor the whole quantum theory.")))))));

    private static DocumentBlock Definition(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula TripleFormula()
    {
        Formula r1 = X("r"), r2 = X("s"), r3 = X("t");
        Formula real = Reals();
        Formula vector = Arrow(FinOf(D(3)), real);
        Formula dot12 = At(Qualified("dotProduct"), r1, r2);
        Formula dot23 = At(Qualified("dotProduct"), r2, r3);
        Formula dot31 = At(Qualified("dotProduct"), r3, r1);
        Formula triple = At(Qualified("dotProduct"), r1,
            At(Qualified("crossProduct"), r2, r3));
        Formula scalar = Add(Add(Add(Typed(D(1), real), dot12), dot23), dot31);
        Formula complexScalar = RealToComplex(scalar);
        Formula rhs = Add(new Formula.Fraction(complexScalar, D(4)),
            new Formula.Fraction(Multiply(RealToComplex(triple), UnitI()), D(4)));
        return All("r", vector, All("s", vector, All("t", vector,
            Equal(Call("tripleBargmann", r1, r2, r3), rhs))));
    }

    private static Formula UnitI() => Seq(Mathrm, Grp(F.Id("i")));
    private static Formula RealToComplex(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula value) => At(Qualified("Fin"), value);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula X(string name) => F.Id(name);
}
