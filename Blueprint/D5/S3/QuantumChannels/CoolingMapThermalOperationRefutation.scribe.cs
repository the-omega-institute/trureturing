using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class CoolingMapThermalOperationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/narasimhachargour2015cooling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-level cooling-map transition cannot be realized by any finite ancilla in its normalized ground-space state and any energy-conserving unitary.",
        H("A cooling transition with no ground-space thermal realization"),
        Blocks(
            Definition("cooling-kraus", "IsCoolingKraus", "Cooling Kraus operators", CoolingKrausFormula(),
                Blocks(Paragraph(Text(
                    "In the increasing energy basis, an allowed Kraus operator is diagonal or a complex multiple of the matrix unit with row j and column k, where j < k. "
                    + "The latter sends the kth energy coordinate to the lower jth coordinate. Zero operators are allowed. "
                    + "This expresses the two classes in LTT_arXiv.tex, arXiv:1409.7740v3, lines 693–700."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("cooling-map", "IsCoolingMap", "Transitions through cooling maps", CoolingMapFormula(),
                Blocks(Paragraph(Text(
                    "There is a finite Kraus family K, each member of which has one of the two allowed forms, whose adjoint products sum to the identity and whose channel sends ρ to σ. "
                    + "This is the state-transition reading of the cooling-map definition in LTT_arXiv.tex, lines 693–700. The completeness identity makes the Kraus channel trace preserving; its Kraus form makes it completely positive. "),
                    Ref("D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus"),
                    Text(" applies the two families by summing K i times ρ times the adjoint of K i. The two family arguments are both K."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("ground-set", "groundSet", "All ground-energy coordinates", GroundSetFormula(),
                Blocks(Paragraph(Text(
                    "For the diagonal ancilla Hamiltonian with real energies e, take every coordinate a whose energy is no greater than the energy of any coordinate b. "
                    + "All degeneracies are retained. This describes the ground eigenspace used in LTT_arXiv.tex, lines 137–141. If m is positive this finite set is nonempty; for m = 0 it is empty."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("ground-state", "groundState", "The normalized ground-space projector", GroundStateFormula(),
                Blocks(Paragraph(Text(
                    "The diagonal entry at a ground coordinate is the inverse of the number of ground coordinates, explicitly cast from a natural number to a complex number; every other entry is zero. "
                    + "For positive m this is the normalized projector onto the entire ground eigenspace. "
                    + "It encodes the idealized state in LTT_arXiv.tex, lines 137–141; line 648 fixes the paper's subsequent low-temperature convention. "
                    + "The definition also permits m = 0, when the matrix has no entries."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("energy-conserving", "IsEnergyConserving", "Commutation with total energy", EnergyConservingFormula(),
                Blocks(Paragraph(Text(
                    "The total Hamiltonian is diagonal on pairs x, with energy E x.1 + e x.2. Each real sum is included in the complex scalars. "
                    + "Energy conservation means that U commutes with this matrix, as in LTT_arXiv.tex, lines 121–134. "
                    + "The predicate accepts an arbitrary complex matrix; unitarity is required separately in the transition assertion."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("thermal-output", "thermalOutput", "The ground-space thermal output", ThermalOutputFormula(),
                Blocks(Paragraph(Text(
                    "Tensor ρ with the ancilla's normalized ground-space projector, conjugate by U, and trace out the ancilla. "
                    + "This combines LTT_arXiv.tex, lines 126–128 and 137–141, with the idealized ground-space convention of line 648. "),
                    Ref("D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight"),
                    Text(" retains the system coordinate and sums the diagonal ancilla coordinates. The definition itself imposes neither unitarity nor energy conservation."))),
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "claim", "The state-transition direction of Conjecture 1",
                Equivalence(Local("claim"), ClaimBody()),
                Blocks(Paragraph(Text(
                    "Conjecture 1 states: \"Cooling maps are equivalent to low-temperature thermal operations, with regard to the feasibility of state transitions.\" "
                    + "LTT_arXiv.tex, lines 924–927, explicitly distinguishes this assertion from equality of the two sets of channels. "
                    + "The formula expresses its cooling-to-thermal direction for every finite system with strictly increasing energies and distinct positive gaps, the assumptions in lines 109–111. "
                    + "Both input and output satisfy "),
                    Ref("D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity"),
                    Text(
                        ", meaning positive semidefiniteness and trace one. The ancilla has positive finite dimension, arbitrary real diagonal energies and its full normalized ground-space state. "
                        + "The unitary is explicitly coerced to a matrix in both occurrences. A change of ancilla energy basis can be absorbed into the unitary. "
                        + "The assertion uses the exact idealized state; it makes no assertion about positive-temperature or approximate transitions."))),
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-level counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 4 and E = (0, 1, 3, 7), with coordinates numbered 0 through 3. The six positive gaps are 1, 2, 3, 4, 6 and 7, all distinct. "
                        + "Let V have rows (1, 0), (0, 1), (3/5, 4/5) and (3/5, 4i/5), where i is the imaginary unit. "
                        + "Put σ = VV†/4 and let K 0 and K 1 be the diagonal matrices formed from the two columns of V. "
                        + "Every row of V has squared norm one, so (K 0)†K 0 + (K 1)†K 1 = I and every diagonal entry of σ is 1/4.")),
                    Paragraph(Text("Use the matrix "),
                        Ref("D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.Pm"),
                        Text(
                            " as ρ: every entry is 1/4. It is vv† for v = (1/2, 1/2, 1/2, 1/2), hence positive semidefinite with trace one. "
                            + "The same properties hold for σ, since VV† is positive semidefinite and σ has four diagonal entries 1/4. "
                            + "The two diagonal Kraus operators send ρ to σ by direct multiplication, proving that the transition is a cooling transition.")),
                    Paragraph(Text(
                        "For any positive finite ancilla dimension m and energy function e, let G be the set of its minimum-energy coordinates and g its cardinality. A finite minimum exists, so g > 0. "
                        + "If U commutes with the total Hamiltonian, its entry U((j,b),(k,a)) vanishes whenever E j + e b differs from E k + e a. "
                        + "For a in G and k < j, minimality of e a and strict increase of E force this inequality of total energies. Thus a ground-space input cannot raise the system energy.")),
                    Paragraph(Text(
                        "Expanding the partial trace of U(ρ ⊗ groundState e)U† gives its (i,j) entry as 1/(4g) times the sum of "
                        + "U((i,b),(k,a)) conjugate(U((j,b),(l,a))) over b, l, a in G and k. "
                        + "For a diagonal output entry, energy conservation and injectivity of E eliminate the terms with k ≠ l. "
                        + "The real population at j is therefore 1/(4g) times the sum of |U((j,b),(k,a))|² over k, a in G and b.")),
                    Paragraph(Text(
                        "Define the real matrix T by T(j,k) = ∑ over a in G and b of |U((j,b),(k,a))|². All entries are nonnegative. "
                        + "If the output is σ, its uniform populations give row sums g. Unitarity gives column sums g, while the downward-energy restriction makes T(j,k) zero for k < j. "
                        + "Comparing row 0 with column 0 forces T(0,1), T(0,2) and T(0,3) to vanish. Comparing row 1 with column 1 then forces T(1,2) and T(1,3) to vanish, "
                        + "and the corresponding comparison at 2 forces T(2,3) to vanish. Thus every off-diagonal entry of T is zero.")),
                    Paragraph(Text(
                        "A zero sum of these nonnegative squared moduli forces every summand to vanish. Hence for a in G, U((j,b),(k,a)) is zero when j ≠ k. "
                        + "When j = k but b is outside G, equality of total energies would imply e b = e a, placing b in G; energy conservation therefore forces these entries to vanish as well. "
                        + "For each k, restrict U to the coordinates (k,a) with a in G and call the resulting square matrix A k. "
                        + "The support just proved reduces U†U = I to (A k)†A k = I on G, so each A k is unitary.")),
                    Paragraph(Text(
                        "Return to the full output-entry expansion. The same support restrictions leave only system indices k = i and l = j, and ancilla indices in G. "
                        + "The remaining sum is trace((A i)(A j)†), so equality of the output with σ gives "
                        + "trace((A i)(A j)†) = g(VV†)(i,j) for all i and j. "
                        + "Expand the squared Hilbert–Schmidt norms of A 2 − (3/5)A 0 − (4/5)A 1 and A 3 − (3/5)A 0 − (4i/5)A 1. "
                        + "Substitution of these trace identities and the displayed rows of V makes both squared norms zero. "
                        + "Consequently A 2 = (3/5)A 0 + (4/5)A 1 and A 3 = (3/5)A 0 + (4i/5)A 1.")),
                    Paragraph(Text(
                        "Set X = (A 0)(A 1)†. Expand the unitary identities (A 2)(A 2)† = I and (A 3)(A 3)† = I using those two linear relations and the unitarity of A 0 and A 1. "
                        + "The first gives X + X† = 0; the second gives X − X† = 0. Thus X = 0. "
                        + "But X is a product of unitaries on the nonempty space indexed by G, hence invertible and nonzero, a contradiction.")),
                    Paragraph(Text(
                        "Finally, applying the asserted transition principle to E, ρ and σ would provide precisely such a positive finite ancilla, energy-conserving unitary and thermal output. "
                        + "The contradiction refutes the stated direction of Conjecture 1. It concerns exact finite ground-space thermal operations and does not assert a result for their approximate or positive-temperature variants."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("narasimhachar-gour-2015-cooling-map-thermal-operation-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, BlockSequence prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            prose, DescribeRole.Definition);

    private static Formula CoolingKrausFormula()
    {
        Formula d = X("d"), kMatrix = X("K"), j = X("j"), k = X("k"), c = X("c");
        Formula lowering = Some("j", FinOf(d), Some("k", FinOf(d),
            Conjunction(Less(j, k), Some("c", Complexes(), Equal(kMatrix,
                Smul(c, At(Qualified("Matrix", "single"), j, k, Typed(D(1), Complexes()))))))));
        return All("d", Naturals(), All("K", MatrixType(FinOf(d)),
            Equivalence(LocalCall("IsCoolingKraus", kMatrix),
                Disjunction(At(Qualified("Matrix", "IsDiag"), kMatrix), lowering))));
    }

    private static Formula CoolingMapFormula()
    {
        Formula d = X("d"), n = X("n"), family = X("K"), i = X("i");
        Formula member = At(family, i);
        Formula complete = Equal(SumOver("i", FinOf(n), Multiply(Adjoint(member), member)),
            Typed(D(1), MatrixType(FinOf(d))));
        Formula ofKraus = Seq(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel",
            "PhyslibLeaf", "MatrixMap", "of"), Underscore, Grp(X("kraus")));
        Formula action = Equal(At(At(ofKraus, family, family), X("ρ")), X("σ"));
        Formula body = Some("n", Naturals(), Some("K", Arrow(FinOf(n), MatrixType(FinOf(d))),
            Conjunction(All("i", FinOf(n), LocalCall("IsCoolingKraus", member)),
                Conjunction(complete, action))));
        return All("d", Naturals(), All("ρ", MatrixType(FinOf(d)), All("σ", MatrixType(FinOf(d)),
            Equivalence(LocalCall("IsCoolingMap", X("ρ"), X("σ")), body))));
    }

    private static Formula GroundSetFormula()
    {
        Formula m = X("m"), e = X("e");
        Formula predicate = LambdaOf("a", FinOf(m), All("b", FinOf(m),
            LessEqual(At(e, X("a")), At(e, X("b")))));
        Formula finiteSet = At(Qualified("Finset"), FinOf(m));
        return All("m", Naturals(), All("e", Arrow(FinOf(m), Reals()),
            Equal(Typed(LocalCall("groundSet", e), finiteSet),
                At(Qualified("Finset", "filter"), predicate, Typed(Qualified("Finset", "univ"), finiteSet)))));
    }

    private static Formula GroundStateFormula()
    {
        Formula m = X("m"), e = X("e");
        Formula cardinality = At(Qualified("Finset", "card"), LocalCall("groundSet", e));
        Formula complexCardinality = Typed(At(Qualified("Nat", "cast"), cardinality), Complexes());
        Formula diagonal = At(Qualified("Matrix", "diagonal"), LambdaOf("a", FinOf(m),
            At(Qualified("ite"), Member(X("a"), LocalCall("groundSet", e)),
                At(Qualified("Inv", "inv"), complexCardinality), Typed(D(0), Complexes()))));
        return All("m", Naturals(), All("e", Arrow(FinOf(m), Reals()),
            Equal(Typed(LocalCall("groundState", e), MatrixType(FinOf(m))), diagonal)));
    }

    private static Formula EnergyConservingFormula()
    {
        Formula x = X("x");
        Formula energy = Add(At(X("E"), At(Qualified("Prod", "fst"), x)),
            At(X("e"), At(Qualified("Prod", "snd"), x)));
        Formula total = At(Qualified("Matrix", "diagonal"), LambdaOf("x", JointIndex(),
            At(Qualified("Complex", "ofReal"), Typed(energy, Reals()))));
        return All("d", Naturals(), All("m", Naturals(),
            All("E", Arrow(FinOf(X("d")), Reals()), All("e", Arrow(FinOf(X("m")), Reals()),
                All("U", MatrixType(JointIndex()), Equivalence(LocalCall("IsEnergyConserving", X("E"), X("e"), X("U")),
                    Equal(Multiply(X("U"), total), Multiply(total, X("U")))))))));
    }

    private static Formula ThermalOutputFormula()
    {
        Formula joint = Multiply(Multiply(X("U"), At(Qualified("Matrix", "kronecker"),
            X("ρ"), LocalCall("groundState", X("e")))), Adjoint(X("U")));
        Formula output = At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"), joint);
        return All("d", Naturals(), All("m", Naturals(), All("e", Arrow(FinOf(X("m")), Reals()),
            All("U", MatrixType(JointIndex()), All("ρ", MatrixType(FinOf(X("d"))),
                Equal(Typed(LocalCall("thermalOutput", X("e"), X("U"), X("ρ")), MatrixType(FinOf(X("d")))), output))))));
    }

    private static Formula ClaimBody()
    {
        Formula d = X("d"), e = X("e"), systemEnergy = X("E");
        Formula unitaryMatrix = Typed(At(Qualified("Subtype", "val"), X("U")), MatrixType(JointIndex()));
        Formula realization = Some("m", Naturals(), Some("e", Arrow(FinOf(X("m")), Reals()),
            Some("U", At(Qualified("Matrix", "unitaryGroup"), JointIndex(), Complexes()),
                Conjunction(Less(Typed(D(0), Naturals()), X("m")),
                    Conjunction(LocalCall("IsEnergyConserving", systemEnergy, e, unitaryMatrix),
                        Equal(LocalCall("thermalOutput", e, unitaryMatrix, X("ρ")), X("σ")))))));
        Formula transitions = All("ρ", MatrixType(FinOf(d)), All("σ", MatrixType(FinOf(d)),
            Implication(Density(X("ρ")), Implication(Density(X("σ")),
                Implication(LocalCall("IsCoolingMap", X("ρ"), X("σ")), realization)))));
        Formula distinctGaps = All("i", FinOf(d), All("j", FinOf(d), All("k", FinOf(d), All("l", FinOf(d),
            Implication(Less(X("i"), X("j")), Implication(Less(X("k"), X("l")),
                Implication(Equal(Subtract(At(systemEnergy, X("j")), At(systemEnergy, X("i"))),
                    Subtract(At(systemEnergy, X("l")), At(systemEnergy, X("k")))),
                    Conjunction(Equal(X("i"), X("k")), Equal(X("j"), X("l"))))))))));
        return All("d", Naturals(), All("E", Arrow(FinOf(d), Reals()),
            Implication(At(Qualified("StrictMono"), systemEnergy), Implication(distinctGaps, transitions))));
    }

    private static Formula Density(Formula matrix) => At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), matrix);
    private static Formula Adjoint(Formula matrix) => At(Qualified("Matrix", "conjTranspose"), matrix);
    private static Formula MatrixType(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula JointIndex() => Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("m"))));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula X(string name) => name switch { "ρ" => Rho, "σ" => SigmaLower, _ => F.Id(name) };
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumChannels", "CoolingMapThermalOperationRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(X(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
}
