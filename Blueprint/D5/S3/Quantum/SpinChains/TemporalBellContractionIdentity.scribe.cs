using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TemporalBellContractionIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/tononilewenstein2025temporalbell");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The endpoint vacuum contractions of the open XX chain equal a difference of one-particle propagator entries.",
        H("Temporal Bell contractions in the open XX chain"),
        Blocks(
            Paragraph(Text(
                "Sites are indexed from zero. Assignment N is the type Fin N → Bool of occupation configurations, "
                + "and FullOperator N is the complex matrix algebra on these configurations. "
                + "The operator fullC j is the Jordan–Wigner annihilator at j; Matrix.conjTranspose is the adjoint. "
                + "Scalar multiplication is denoted by a centered dot, and adjacent matrix factors are multiplied in their displayed order. "
                + "Complex.ofReal explicitly includes a real scalar in the complex numbers, and Fin.val takes a bounded index to its natural value. "
                + "Natural subtraction is truncated at zero. Fin.mk displays its natural value with the bound proof suppressed; "
                + "the positivity proof in sigmaXLast is also suppressed when it is determined by the hypothesis N ≥ 2. "
                + "All other binders, including the positivity argument in the definition of sigmaXLast, are displayed.")),
            Node("hopping", "The open-chain one-particle Hamiltonian", HoppingFormula(),
                "The diagonal entries are minus the chemical potential μ. Nearest-neighbor entries are minus the hopping strength J, "
                + "and all other entries vanish. This is the one-particle matrix of the fermionic Hamiltonian in the source, "
                + "arxiv.tex lines 144–150; only sites with adjacent natural indices are coupled.",
                AssessedProvenance.FromLiterature(Source)),
            Node("hamiltonian", "The quadratic many-particle Hamiltonian", HamiltonianFormula(),
                "Sum the creation-annihilation products with coefficients from hopping. "
                + "This is the source's Jordan–Wigner form of the open XX Hamiltonian, arxiv.tex lines 144–150, "
                + "on the full occupation space. The sums and the definition include the empty chain.",
                AssessedProvenance.FromLiterature(Source)),
            Node("propagator", "The propagator defined by the matrix exponential", PropagatorFormula(),
                "The complex matrix exponential of it times the one-particle Hamiltonian gives the coefficients of evolved creation operators. "
                + "Thus G is read through the source's relation f†ⱼ(t) = ∑ᵢ Gᵢⱼ(t)f†ᵢ in arxiv.tex lines 153–154 and 291. "
                + "The definition fixes the hopping sign through hopping and does not use the printed spectral expression for the eigenfunctions.",
                AssessedProvenance.FromRepo(Source)),
            Node("evolve", "Heisenberg evolution", EvolveFormula(),
                "Conjugate A by the exponential of itH, with the inverse exponential on the right. "
                + "This is the Heisenberg convention used for the creation operators in arxiv.tex line 291. "
                + "All three parameters J, μ and t are real; no sign restriction is imposed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sigmaXLast", "The last-site spin observable", SigmaXLastFormula(),
                "For a positive chain length, multiply the factors 1 − 2f†ⱼfⱼ over the sites strictly before N − 1, "
                + "in increasing order, and then multiply by f† at the last site plus f at that site. "
                + "List.finRange supplies the increasing list of sites, List.filter retains the prefix, List.map forms the factors, "
                + "and List.prod multiplies them. The Boolean filter explicitly decides the natural inequality. "
                + "This is σˣ at the last site under the inverse Jordan–Wigner transformation, arxiv.tex lines 285–286 and 291.",
                AssessedProvenance.FromLiterature(Source)),
            Node("vacuumIndex", "The empty occupation configuration", VacuumIndexFormula(),
                "The pointwise defining equality states that the vacuum has false occupation at every site. Its row and column select the vacuum matrix element of any full operator. "
                + "The argument x ranges over Fin N, including the empty type when N is zero.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "The endpoint contraction identity", ClaimFormula(),
                "For every N at least two and every real J, μ and t, evolve the last-site spin observable and evaluate the two displayed "
                + "vacuum contractions. Their sum has the same real part as the last diagonal propagator entry minus its first-row, last-column entry. "
                + "This reads the conjecture in arxiv.tex lines 343–353 with G defined by the creation-operator evolution relation. "
                + "The hypothesis N ≥ 2 makes first and last distinct and supplies the positive chain length needed by sigmaXLast.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("temporal-bell-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The identity for every chain length at least two"),
                StatementSource.FromAuthor(Disp(ContractionStatement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write fⱼ = fullC j, h = hopping N J μ and H = hamiltonian N J μ. "
                        + "Taking adjoints of the distinct-site annihilation anticommutators gives the corresponding creation anticommutators. "
                        + "At a single site, write the two Majorana operators as fⱼ + f†ⱼ and i(fⱼ − f†ⱼ); "
                        + "their Clifford relations give four times the creation self-anticommutator equal to zero, hence that anticommutator vanishes. "
                        + "Together with the mixed canonical anticommutation relation, these identities imply "
                        + "[f†ᵢfₖ, f†ⱼ] = δₖⱼf†ᵢ. Summing with the hopping coefficients gives [H,f†ⱼ] = ∑ᵢ hᵢⱼf†ᵢ.")),
                    Paragraph(Text(
                        "For a fixed j, let L(M) = ∑ᵢ Mᵢⱼf†ᵢ, a complex linear map from one-particle matrices to full operators. "
                        + "The commutator identity gives H L(M) − L(M) H = L(hM). "
                        + "For complex z, differentiate F(z) = exp(−zH)L(exp(zh))exp(zH). "
                        + "The product rule and the commutator identity cancel all three derivative terms, so F has derivative zero everywhere and is constant. "
                        + "At zero, L(1) = f†ⱼ. Multiplying by the inverse exponentials and setting z = Complex.ofReal(t)i therefore gives "
                        + "evolve J μ t f†ⱼ = ∑ᵢ Gᵢⱼ(t)f†ᵢ. "
                        + "The hopping matrix has conjugate-symmetric entries; taking the adjoint of the finite double sum and interchanging its indices proves H Hermitian. "
                        + "Consequently evolution preserves adjoints, and taking the adjoint of the creation formula gives "
                        + "evolve J μ t fⱼ = ∑ᵢ conjugate(Gᵢⱼ(t))fᵢ.")),
                    Paragraph(Text(
                        "Let P be number parity. Its anticommutation with the two Majorana operators, separated into their sum and difference, "
                        + "shows that P anticommutes with each fⱼ and f†ⱼ. "
                        + "In the occupation basis, f†ⱼfⱼ is diagonal with entry one exactly when site j is occupied. "
                        + "Thus 1 − 2f†ⱼfⱼ is diagonal with entry minus one at an occupied site and plus one at an empty site. "
                        + "Multiplying these diagonal matrices over the prefix and then the last site gives P, whose entry is minus one to the total occupation count. "
                        + "The creation self-anticommutator and CAR_nilpotent give (f†ⱼ)² = 0; taking adjoints gives fⱼ² = 0. "
                        + "The single-site mixed relation then yields (1 − 2f†ⱼfⱼ)(fⱼ − f†ⱼ) = f†ⱼ + fⱼ. "
                        + "Combining the prefix product with this equality expresses the last-site spin observable as P(f_last − f†_last).")),
                    Paragraph(Text(
                        "Moving P through one creation operator and one annihilation operator changes the sign twice, so P commutes with every f†ᵢfⱼ and hence with H. "
                        + "Its Heisenberg evolution is therefore P. Conjugation by an invertible exponential preserves products and differences. "
                        + "Applying these facts and the two evolution formulas gives the evolved last-site spin observable as "
                        + "P(∑ᵢ conjugate(Gᵢ,last(t))fᵢ − ∑ᵢ Gᵢ,last(t)f†ᵢ).")),
                    Paragraph(Text(
                        "Every annihilator kills the empty occupation column, and every creator kills its adjoint row. "
                        + "The mixed anticommutation relation then gives ⟨0|fᵢf†ⱼ|0⟩ = δᵢⱼ. "
                        + "For arbitrary sites a, b, k and r, commute the two creators to the left to obtain "
                        + "⟨0|f_b f_a f†_k f†_r|0⟩ = δₐₖδᵦᵣ − δᵦₖδₐᵣ. "
                        + "Commuting the last creator past an annihilator also gives ⟨0|f_b f_a f_k f†_r|0⟩ = 0. "
                        + "For a ≠ b and arbitrary coefficient functions u and v, move P to the left through f_b f_a. "
                        + "The two sign changes cancel and the vacuum row of P has value one, so parity disappears from the contractions. "
                        + "Expanding the sums, the annihilation terms vanish and the four-operator formula shows that the contraction with f†_a equals v b, "
                        + "while the contraction with f†_b equals −v a. Their sum is v b − v a.")),
                    Paragraph(Text(
                        "Take a = first, b = last, u i = conjugate(Gᵢ,last(t)) and v i = Gᵢ,last(t). "
                        + "Since N ≥ 2, first and last are distinct. Substitution of the evolved observable therefore proves the complex identity: "
                        + "the two vacuum contractions sum to G_last,last(t) − G_first,last(t). Taking Complex.re of both sides gives the stated real-part identity."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tononi-lewenstein-2025-temporal-bell-contraction-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("temporal-bell-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula HoppingFormula()
    {
        Formula neighbors = Or(
            Equal(Add(At(Q("Fin", "val"), V("i")), Typed(D(1), Naturals)), At(Q("Fin", "val"), V("j"))),
            Equal(Add(At(Q("Fin", "val"), V("j")), Typed(D(1), Naturals)), At(Q("Fin", "val"), V("i"))));
        Formula entries = LambdaOf("i", FinN, LambdaOf("j", FinN,
            If(Equal(V("i"), V("j")), Negative(OfReal(Mu)),
                If(neighbors, Negative(OfReal(V("J"))), Typed(D(0), Complexes)))));
        return Parameters(Equal(Typed(Call("hopping", V("N"), V("J"), Mu), OneParticleMatrix), entries));
    }

    private static Formula HamiltonianFormula() => Parameters(Equal(
        Typed(Call("hamiltonian", V("N"), V("J"), Mu), FullOperator),
        SumOver("i", FinN, SumOver("j", FinN,
            Smul(Call("hopping", V("N"), V("J"), Mu, V("i"), V("j")),
                Multiply(Adjoint(Annihilator(V("i"))), Annihilator(V("j"))))))));

    private static Formula PropagatorFormula() => Parameters(All("t", Reals, Equal(
        Typed(Call("propagator", V("N"), V("J"), Mu, V("t")), OneParticleMatrix),
        Exponential(Smul(TimeScalar, Call("hopping", V("N"), V("J"), Mu))))));

    private static Formula EvolveFormula() => Parameters(All("t", Reals, All("A", FullOperator,
        Equal(Typed(Call("evolve", V("J"), Mu, V("t"), V("A")), FullOperator),
            Multiply(Multiply(Exponential(Generator), V("A")), Exponential(Negative(Generator)))))));

    private static Formula SigmaXLastFormula()
    {
        Formula prefix = At(Q("List", "filter"),
            LambdaOf("j", FinN, At(Q("Decidable", "decide"),
                LessThan(At(Q("Fin", "val"), V("j")), LastValue))),
            At(Q("List", "finRange"), V("N")));
        Formula factor = Subtract(Typed(D(1), FullOperator),
            Smul(Typed(D(2), Complexes), Multiply(Adjoint(Annihilator(V("j"))), Annihilator(V("j")))));
        Formula product = At(Q("List", "prod"), At(Q("List", "map"), LambdaOf("j", FinN, factor), prefix));
        Formula last = Typed(At(Q("Fin", "mk"), LastValue), FinN);
        return All("N", Naturals, All("hN", LessThan(Typed(D(0), Naturals), V("N")),
            Equal(Typed(Call("sigmaXLast", V("N"), V("hN")), FullOperator),
                Multiply(product, Add(Adjoint(Annihilator(last)), Annihilator(last))))));
    }

    private static Formula VacuumIndexFormula() => All("N", Naturals, All("x", FinN,
        Equal(At(Typed(Call("vacuumIndex", V("N")), Assignment), V("x")), Q("Bool", "false"))));

    private static Formula ClaimFormula() => Equal(Typed(Call("claim"), Q("Prop")), Parenthesized(ContractionStatement()));

    private static Formula ContractionStatement()
    {
        Formula vacuum = Call("vacuumIndex", V("N"));
        Formula common = Multiply(Multiply(Annihilator(V("last")), Annihilator(V("first"))), V("X"));
        Formula firstTerm = At(Parenthesized(Multiply(common, Adjoint(Annihilator(V("first"))))), vacuum, vacuum);
        Formula lastTerm = At(Parenthesized(Multiply(common, Adjoint(Annihilator(V("last"))))), vacuum, vacuum);
        Formula difference = Subtract(
            Call("propagator", V("N"), V("J"), Mu, V("t"), V("last"), V("last")),
            Call("propagator", V("N"), V("J"), Mu, V("t"), V("first"), V("last")));
        Formula identity = Equal(At(Q("Complex", "re"), Parenthesized(Add(firstTerm, lastTerm))),
            At(Q("Complex", "re"), Parenthesized(difference)));
        Formula body = Let("first", FinN, Typed(At(Q("Fin", "mk"), Typed(D(0), Naturals)), FinN),
            Let("last", FinN, Typed(At(Q("Fin", "mk"), LastValue), FinN),
                Let("X", FullOperator, Call("evolve", V("J"), Mu, V("t"), Call("sigmaXLast", V("N"))), identity)));
        return All("N", Naturals, new Formula.Logic(
            Parenthesized(LessOrEqual(Typed(D(2), Naturals), V("N"))), FormulaLogicOperator.Implies,
            Parenthesized(All("J", Reals, All("μ", Reals, All("t", Reals, body))))));
    }

    private static Formula Parameters(Formula body) => All("N", Naturals, All("J", Reals, All("μ", Reals, body)));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinN => Call("Fin", V("N"));
    private static Formula Assignment => Call("Assignment", V("N"));
    private static Formula FullOperator => Call("FullOperator", V("N"));
    private static Formula OneParticleMatrix => Call("Matrix", FinN, FinN, Complexes);
    private static Formula LastValue => Subtract(V("N"), Typed(D(1), Naturals));
    private static Formula TimeScalar => Multiply(OfReal(V("t")), Q("Complex", "I"));
    private static Formula Generator => Smul(TimeScalar, Call("hamiltonian", V("N"), V("J"), Mu));
    private static Formula V(string name) => name == "μ" ? Mu : F.Id(name);
    private static Formula OfReal(Formula value) => At(Q("Complex", "ofReal"), value);
    private static Formula Annihilator(Formula j) => Call("fullC", j);
    private static Formula Adjoint(Formula value) => At(Q("Matrix", "conjTranspose"), value);
    private static Formula Exponential(Formula value) => At(Q("NormedSpace", "exp"), value);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : At(Q(name), args);
    private static Formula Q(params string[] parts)
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Q("let"), Sp, Typed(V(name), type), Sp, Colon, Eq, Sp, Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Q("ite"), Parenthesized(condition), Parenthesized(yes), Parenthesized(no));
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThan(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
}
