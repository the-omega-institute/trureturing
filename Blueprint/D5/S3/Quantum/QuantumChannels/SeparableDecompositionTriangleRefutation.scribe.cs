using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SeparableDecompositionTriangleRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/toth2026wassersteinfidelities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three block-supported mixed states have decomposition transport distances with a long side of square root three and a two-edge route of length at most square root two.",
        H("A mixed middle state breaks the decomposition transport triangle inequality"),
        Blocks(
            Node("expectation", "Pure-vector observable expectation", ExpectationFormula(),
                "The vector ψ has complex coordinates indexed by Fin d. The expression is the real part of the conjugate-vector dot product with Hψ. For a unit ψ and Hermitian H, it is the usual expectation in |ψ⟩⟨ψ|. The definition also makes sense without either hypothesis. This is the expectation appearing in the pure-state reduction of equation (12).",
                AssessedProvenance.FromLiterature(Source)),
            Node("pureCost", "The modified pure-state squared cost", PureCostFormula(),
                "For every finite family H, take half the sum of squared differences of the real observable expectations. On unit vectors and Hermitian observables this is the modified pure-state value in equation (12): pure marginals force the coupling |ψ⟩⟨ψ|ᵀ ⊗ |φ⟩⟨φ|. The transpose trace identity Tr(Hᵀϱᵀ) = Tr(Hϱ) preserves the observable expectations. Expanding each squared difference operator gives the sum of the two variances plus the squared difference of means. The factor 1/2 multiplies both parts. The two self-costs are the respective sums of variances, so subtracting their average cancels the variance terms. This correspondence to equation (12) is a mathematical explanation and is not formalized here. The definition is precisely the displayed expectation formula.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Decomposition", "A common-weight pair of finite pure ensembles", DecompositionFormula(),
                "Equations (18) and (19) use a common finite probability distribution. The structure stores a natural length K, nonnegative real weights p with total mass one, and two families of complex vectors ψ and φ indexed by Fin K. Every vector is unit, including those with zero weight. The two weighted sums of rankOneDensity are exactly ρ and σ. Here rankOneDensity is the existing unnormalized outer product v v*, and the unit identities make these particular outer products trace-one. The displayed dependent tuple represents the fields of this structure; no orthogonality, block support, fixed ensemble size, or relation between the paired vectors is assumed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("costs", "All admissible decomposition costs", CostsFormula(),
                "The set contains the weighted pureCost average for every Decomposition of the two supplied matrices. Its elements range over all finite ensemble lengths and every common probability distribution, as in equation (83). The notation p(q), ψ(q), φ(q), and K(q) selects the corresponding structure fields. The existential does not restrict to the concrete ensembles used below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("decompSq", "The squared decomposition quantity", DistanceFormula(true),
                "Equation (83) is expressed as the real infimum of the whole admissible finite cost set. Real sInf is total, including its zero convention for an empty set or a set unbounded below; the counterexample uses nonempty sets bounded below by zero. Every square in pureCost is nonnegative, and every admissible weight is nonnegative.\n" +
                "For positive dimension, density marginals and Hermitian observables, the following mathematical explanation identifies this finite infimum with the source minimum; it is not formalized here. Pure-state projectors form a compact space. The pureCost depends only on the projectors P and Q, and the map (P,Q) ↦ (P,Q,pureCost(P,Q)) is continuous into the finite-dimensional real space of two Hermitian matrices and a cost coordinate. Its convex hull is compact. The slice fixing the two density marginals is nonempty, since spectral decompositions with product weights give a finite common-weight ensemble. The cost coordinate attains its minimum on this compact slice. Carathéodory's theorem gives a finite representation of a minimizer, so the minimum is a finite-decomposition cost and equals sInf. A countable decomposition has its marginal-and-cost barycenter in the same closed convex hull: the image is compact and bounded, and partial probability sums completed by their remaining mass converge to that barycenter. Thus countable decompositions cannot lower the optimum. Rank-one projectors admit unit-vector representatives, giving the vector fields in Decomposition. This compactness, attainment, finite-representation and countable-extension correspondence is mathematical explanation, not a formalized theorem.",
                AssessedProvenance.FromLiterature(Source)),
            Node("decomp", "The decomposition distance", DistanceFormula(false),
                "Take the nonnegative real square root of decompSq. This is the quantity denoted by the modified decomposition distance in equation (83), with the explicitly stated pure-state correspondence above.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The triangle assertion with an arbitrary middle state", ClaimFormula(),
                "Section III.3.3 asks whether these quantities fulfill the triangle inequality. The assertion here ranges over all natural dimensions d and observable counts N, every family of Hermitian complex d by d matrices, and every triple of density matrices ρ, ω, τ. IsDensity is the existing positive-semidefinite, trace-one predicate. In particular ω need not be pure. Theorem 10 proves the pure-middle-state case; its hypothesis is retained in that source theorem but is absent from the universal extension considered here.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A six-dimensional counterexample with a mixed middle state",
                Disp(new Formula.Not(Call("claim"))),
                "Use blocks A = {0,1}, B = {2,3}, C = {4,5}, and their density matrices ρA = ΠA/2, ρB = ΠB/2, ρC = ΠC/2. Let X,Y,Z be the Pauli matrices. The seven observables, written as triples of two by two diagonal blocks, are (X,X,0), (Y,Z,0), (Z,0,0), (0,Y,X), (0,0,Y), (0,0,Z), and L = diag(0,0,1,1,2,2). All seven are Hermitian. For a pure state in A with Bloch vector (x,y,z), the first six expectations are (x,y,z,0,0,0). In B they are (x,z,0,y,0,0), and in C they are (0,0,0,x,y,z). The last expectation is respectively 0, 1, or 2.\n" +
                "For the A-to-B side, pair the two X eigenvectors (1,±1)/√2 in A with the matching X eigenvectors in B, each with weight 1/2. Their first six expectations agree and their L expectations differ by one, giving cost 1/2. For the B-to-C side, pair the Y eigenvectors (1,±i)/√2 in B with the matching X eigenvectors in C, again with weights 1/2. Their fourth expectations agree and every other Pauli expectation vanishes; L again gives cost 1/2. Both mixtures have the required block marginals. Thus each short squared infimum is at most 1/2.\n" +
                "For any admissible A-to-C ensemble, the diagonal entries outside A give sums of nonnegative terms pₖ|ψₖ(j)|² equal to zero. At every positive weight all outside components therefore vanish. The corresponding statement holds outside C for φ. A unit vector in either two-dimensional block has a unit Bloch vector. The two Bloch vectors occupy disjoint observable coordinates, so their squared expectation differences sum to 1 + 1; the L difference contributes 4. Hence every positive-weight pair has pureCost 3. Zero-weight terms contribute zero and the weights sum to one, so every admissible total cost is 3. An explicit finite ensemble makes the set nonempty, and the long squared infimum is therefore 3.\n" +
                "Taking square roots, the long side is √3 and the two short sides sum to at most 2√(1/2) = √2. Since √3 > √2, claim is false. The middle density matrix is mixed and has the two different ensembles used on the short sides. This construction answers the general mixed-middle-state question; it does not contradict the pure-middle-state theorem.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("toth-pitrik-2026-separable-decomposition-triangle"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("tpdecomptriangle-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(prose.Split('\n').Select(part => Paragraph(Text(part))).ToArray()), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) => arguments.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula IffTo(Formula left, Formula right) => new Formula.Logic(Par(left), FormulaLogicOperator.Iff, Par(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Par(left), FormulaBinaryOperator.Multiply, Par(right));
    private static Formula Arr(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Sq(Formula value) => new Formula.Power(Par(value), D(2));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Vec(Formula size) => Arr(Fin(size), Complex());
    private static Formula Mat(Formula size) => Call("Matrix", Fin(size), Fin(size), Complex());
    private static Formula Family(Formula size, Formula count) => Arr(Fin(count), Mat(size));
    private static Formula SetOf(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula SumIn(Formula variable, Formula domain, Formula value) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, InMacro, Sp, domain)), Sp, value);
    private static Formula ForFamily(Formula body) => All(F.Id("d"), Nat(), All(F.Id("N"), Nat(),
        All(F.Id("H"), Family(F.Id("d"), F.Id("N")), body)));
    private static Formula ForStates(Formula body) => All(Rho, Mat(F.Id("d")), All(SigmaLower, Mat(F.Id("d")), body));
    private static Formula Unit(Formula vector) => Eqn(Call("dotProduct", Call("star", vector), vector), D(1));

    private static Formula ExpectationFormula()
    {
        Formula d = F.Id("d"), h = F.Id("H"), psi = Psi;
        return Disp(All(d, Nat(), All(h, Mat(d), All(psi, Vec(d),
            Eqn(Call("expectation", h, psi), Call("re", Call("dotProduct", Call("star", psi), Call("mulVec", h, psi))))))));
    }

    private static Formula PureCostFormula()
    {
        Formula h = F.Id("H"), n = F.Id("n");
        return Disp(ForFamily(All(Psi, Vec(F.Id("d")), All(Phi, Vec(F.Id("d")),
            Eqn(Call("pureCost", h, Psi, Phi), Mul(new Formula.Fraction(D(1), D(2)),
                SumIn(n, Fin(F.Id("N")), Sq(Sub(Call("expectation", At(h, n), Psi),
                    Call("expectation", At(h, n), Phi))))))))));
    }

    private static Formula DecompositionFormula()
    {
        Formula d = F.Id("d"), k = F.Id("K"), p = F.Id("p"), i = F.Id("k");
        Formula tuple = Par(Seq(k, Comma, Sp, p, Comma, Sp, Psi, Comma, Sp, Phi));
        Formula data = Seq(Sigma, Sp, Par(Seq(k, Colon, Sp, Nat())), Comma, Sp,
            Par(Arr(Fin(k), Real())), Sp, Times, Sp, Par(Arr(Fin(k), Vec(d))), Sp, Times, Sp, Par(Arr(Fin(k), Vec(d))));
        Formula conditions = And(All(i, Fin(k), Leq(D(0), At(p, i))),
            And(Eqn(SumIn(i, Fin(k), At(p, i)), D(1)),
            And(All(i, Fin(k), Unit(At(Psi, i))),
            And(All(i, Fin(k), Unit(At(Phi, i))),
            And(Eqn(SumIn(i, Fin(k), Mul(Call("ofReal", At(p, i)), Call("rankOneDensity", At(Psi, i)))), Rho),
                Eqn(SumIn(i, Fin(k), Mul(Call("ofReal", At(p, i)), Call("rankOneDensity", At(Phi, i)))), SigmaLower))))));
        return Disp(All(d, Nat(), ForStates(Eqn(Call("Decomposition", Rho, SigmaLower), SetOf(tuple, data, conditions)))));
    }

    private static Formula CostsFormula()
    {
        Formula q = F.Id("q"), c = F.Id("c"), k = F.Id("k"), h = F.Id("H");
        Formula value = SumIn(k, Fin(Call("K", q)), Mul(At(Call("p", q), k),
            Call("pureCost", h, At(Call("psi", q), k), At(Call("phi", q), k))));
        return Disp(ForFamily(ForStates(Eqn(Call("costs", h, Rho, SigmaLower),
            SetOf(c, Real(), Some(q, Call("Decomposition", Rho, SigmaLower), Eqn(c, value)))))));
    }

    private static Formula DistanceFormula(bool squared)
    {
        Formula h = F.Id("H");
        return Disp(ForFamily(ForStates(Eqn(Call(squared ? "decompSq" : "decomp", h, Rho, SigmaLower),
            squared ? Call("sInf", Call("costs", h, Rho, SigmaLower))
                : Call("sqrt", Call("decompSq", h, Rho, SigmaLower))))));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("H"), n = F.Id("n"), omega = Omega;
        Formula hermitian = All(n, Fin(F.Id("N")), Call("IsHermitian", At(h, n)));
        Formula inequality = Leq(Call("decomp", h, Rho, Tau),
            Add(Call("decomp", h, Rho, omega), Call("decomp", h, omega, Tau)));
        Formula states = All(Rho, Mat(F.Id("d")), All(omega, Mat(F.Id("d")), All(Tau, Mat(F.Id("d")),
            Imp(Call("IsDensity", Rho), Imp(Call("IsDensity", omega), Imp(Call("IsDensity", Tau), inequality))))));
        return Disp(IffTo(Call("claim"), ForFamily(Imp(hermitian, states))));
    }
}
