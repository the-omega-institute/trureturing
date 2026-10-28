using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LevelOneQAOAGenuineSuperpositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuadraticForms/streifleib2020forbidden");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level-one QAOA on three qubits reaches a genuine superposition of exactly four computational basis states.",
        H("A genuine four-state superposition from level-one QAOA"),
        Blocks(
            Definition("mixer", "The transverse-field mixer", MixerFormula(),
                "The mixer is the sum, over all qubits, of the permutation matrices that flip that qubit and leave the others fixed. "
                    + "Each summand is a single-qubit Pauli-X operator on the computational basis Fin n → Bool. "
                    + "This is the mixing Hamiltonian in main.tex, lines 104–105, of the source.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("qaoaState", "One phase layer and one mixing layer", StateFormula(),
                "The real function e assigns an energy to every computational basis state. "
                    + "Its values are included in the complex scalars to form the diagonal Hamiltonian. "
                    + "Starting from the uniform state plusState n, apply the diagonal Hamiltonian propagator for time γ, "
                    + "then the mixer propagator for time β. Each propagator is the matrix exponential exp(−itH). "
                    + "This is the one-layer case of the ansatz in main.tex, lines 104–110; the diagonal energies are specified at line 124.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("IsGenuineSuperposition", "Exact nonvanishing support", GenuineFormula(),
                "A vector ψ is a genuine superposition of t when its amplitude is nonzero at exactly the basis states belonging to t. "
                    + "Thus every amplitude on t is nonzero and every amplitude outside t vanishes. "
                    + "The predicate imposes no normalization condition on an arbitrary vector. "
                    + "The source's notion of a genuine superposition appears in main.tex, line 336.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "The exclusion of intermediate target dimensions", ClaimFormula(),
                "The exclusion asserts that every real diagonal energy function, at every pair of real angles, fails to produce "
                    + "a genuine superposition of any target set whose cardinality is strictly between two and two to the power n. "
                    + "This is the unrestricted reading of the exclusion stated in the abstract, main.tex line 71. "
                    + "The argument at line 336 assumes that only odd multiples of π/4 can solve the necessary condition; "
                    + "line 341 states that angle restriction as a conjecture. The displayed assertion contains no such restriction "
                    + "and imposes no condition relating t to the ground states of e.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("level-one-qaoa-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four nonzero amplitudes at mixing angle π/8"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take three qubits. Let T consist of the bit strings x with x 0 ≠ x 1, "
                            + "and let the energy be 2π when x 0 = x 1 and π/2 otherwise. "
                            + "Choose γ = 1 and β = π/8. Let u be the vector with every coordinate equal to one, "
                            + "and let p have coordinate one when the first two bits agree and minus one when they differ.")),
                    Paragraph(Text(
                        "Multiplication by the mixer sums a vector's values over the three single-bit flips. "
                            + "It therefore sends u to 3u. Flipping either of the first two bits negates p, while flipping the third preserves p, "
                            + "so it sends p to −p. The exponential action on an eigenvector then gives the mixing phases "
                            + "exp(−3βi) on u and exp(βi) on p.")),
                    Paragraph(Text(
                        "The uniform initial amplitude is a, the inverse of the complex inclusion of √8. "
                            + "This agrees with the three-qubit amplitude (√2)⁻³ because √8 = (√2)³. "
                            + "The diagonal exponential acts coordinate by coordinate. At time one its phases are exp(−2πi) = 1 "
                            + "where the first two bits agree and exp(−πi/2) = −i where they differ. "
                            + "Consequently the phase layer produces a(1−i)u/2 + a(1+i)p/2.")),
                    Paragraph(Text(
                        "At β = π/8 the identity −3βi = −πi/2 + βi gives exp(−3βi) = −i exp(βi). "
                            + "Apply the two mixing phases to the preceding decomposition. Where p equals one the two contributions cancel. "
                            + "Where p equals minus one they sum to −a(1+i)exp((π/8)i). "
                            + "Thus the output amplitude is zero exactly when the first two bits agree, "
                            + "and is the same nonzero coefficient at every other coordinate.")),
                    Paragraph(Text(
                        "The coefficient is nonzero: √8 is strictly positive, its complex inverse and its negative are nonzero, "
                            + "1+i has positive real part, and a complex exponential never vanishes. "
                            + "Enumerating the three-bit strings gives T = {010, 011, 100, 101} and cardinality four. "
                            + "The amplitude formula therefore proves that the output is a genuine superposition of T. "
                            + "Since 2 < 4 < 2³, applying the exclusion to these energies, angles and target set "
                            + "contradicts that genuine superposition."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("streif-leib-2020-level-one-qaoa-genuine-superposition"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("level-one-qaoa-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MixerFormula()
    {
        Formula identities = At(Qualified("Function", "const"), FinOf(X("n")),
            At(Qualified("Equiv", "refl"), Qualified("Bool")));
        Formula flip = At(Qualified("Equiv", "piCongrRight"),
            At(Qualified("Function", "update"), identities, X("i"), Qualified("Equiv", "boolNot")));
        Formula summand = At(Qualified("Equiv", "Perm", "permMatrix"), Complexes(), flip);
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(X("i"), FinOf(X("n")))), Sp,
            Parenthesized(summand));
        return All("n", Naturals(), Equal(Typed(LocalCall("mixer", X("n")),
            At(Qualified("Matrix"), Bits(), Bits(), Complexes())), sum));
    }

    private static Formula StateFormula()
    {
        Formula diagonal = At(Qualified("Matrix", "diagonal"), LambdaOf("x", Bits(),
            At(Qualified("Complex", "ofReal"), At(X("e"), X("x")))));
        Formula phase = MulVec(Propagator(diagonal, X("γ")),
            At(Qualified("D5", "S3", "Quantum", "Entanglement", "RandomizedGraphNegativityRefutation", "plusState"), X("n")));
        return All("n", Naturals(), All("e", Arrow(Bits(), Reals()), All("β", Reals(), All("γ", Reals(),
            Equal(Typed(LocalCall("qaoaState", X("n"), X("e"), X("β"), X("γ")), Arrow(Bits(), Complexes())),
                MulVec(Propagator(LocalCall("mixer", X("n")), X("β")), phase))))));
    }

    private static Formula GenuineFormula() => All("n", Naturals(), All("ψ", Arrow(Bits(), Complexes()),
        All("t", At(Qualified("Finset"), Bits()), Equivalence(LocalCall("IsGenuineSuperposition", X("ψ"), X("t")),
            All("x", Bits(), Equivalence(NotEqual(At(X("ψ"), X("x")), Typed(D(0), Complexes())),
                new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf, X("t"))))))));

    private static Formula ClaimFormula()
    {
        Formula cardinality = At(Qualified("Finset", "card"), X("t"));
        Formula exclusion = new Formula.Not(Parenthesized(LocalCall("IsGenuineSuperposition",
            LocalCall("qaoaState", X("n"), X("e"), X("β"), X("γ")), X("t"))));
        return Equivalence(Local("claim"), All("n", Naturals(), All("e", Arrow(Bits(), Reals()),
            All("β", Reals(), All("γ", Reals(), All("t", At(Qualified("Finset"), Bits()),
                Arrow(Less(Typed(D(2), Naturals()), cardinality),
                    Arrow(Less(cardinality, new Formula.Power(Typed(D(2), Naturals()), X("n"))), exclusion))))))));
    }

    private static Formula Propagator(Formula matrix, Formula time) =>
        At(Qualified("D5", "S3", "Quantum", "Dynamics", "ProjectionProbabilityFlow", "hamiltonianPropagator"), matrix, time);
    private static Formula MulVec(Formula matrix, Formula vector) => At(Qualified("Matrix", "mulVec"), matrix, vector);
    private static Formula Bits() => Arrow(FinOf(X("n")), Qualified("Bool"));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Dynamics", "LevelOneQAOAGenuineSuperposition", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "β" => Beta,
        "γ" => GammaLower,
        "ψ" => Psi,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
