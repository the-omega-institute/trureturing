using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class ComplexHoppingCoherenceDampingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/sokolovs2026paritysuperselection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex hopping can increase parity-twisted ground-state coherences.",
        H("Coherence damping fails for complex hopping"),
        Blocks(
            Node("Fock", "Occupation configurations", FockFormula(),
                "Fock(N) is the occupation basis of N ordered modes, with each occupation in Fin 2. The Hilbert space consists of complex functions on this basis and has dimension 2ᴺ. val takes the natural value of a finite index.", AssessedProvenance.FromRepo()),
            Node("Operator", "Operators on fermionic Fock space", OperatorFormula(),
                "An operator is a complex matrix whose row and column labels are occupation configurations. Matrix multiplication and the conjugate transpose use this basis.", AssessedProvenance.FromRepo()),
            Node("annihilator", "Jordan–Wigner annihilation", AnnihilatorFormula(),
                "The entry is nonzero precisely when mode j is occupied in the input t and the output s empties that mode. Its sign counts the occupied modes before j. update(t,j,0) changes only occupation j; the sum in the exponent is a natural-number sum.", AssessedProvenance.FromRepo()),
            Node("hamiltonian", "Number-conserving quadratic Hamiltonians", HamiltonianFormula(),
                "The matrix h acts on the single-particle space. Its second quantization sums creation at j followed by annihilation at k. The dagger denotes conjugate transpose; no Hermiticity assumption is needed to define this operator.", AssessedProvenance.FromRepo()),
            Node("Normalized", "Unit Fock vectors", NormalizedFormula(),
                "The sum of squared moduli is one. The bar denotes complex conjugation.", AssessedProvenance.FromRepo()),
            Node("energy", "The real quadratic form", EnergyFormula(),
                "Energy is the real part of the quadratic form, defined for every operator. For a Hermitian operator it is the usual expectation value.", AssessedProvenance.FromRepo()),
            Node("IsGroundState", "Variational ground states", GroundStateFormula(),
                "A ground state is normalized and minimizes energy among all normalized Fock vectors. The comparison includes every particle-number sector.", AssessedProvenance.FromRepo()),
            Node("AdjacentPartition", "Three adjacent blocks and their complement", PartitionFormula(),
                "The five natural lengths are ordered left, A, B, D, right. The complement E consists of both outer blocks. The displayed set describes the structure's five lengths and its size equality; zero lengths are allowed. For a partition p, left(p), a(p), b(p), d(p), right(p) and size(p) denote its fields.", AssessedProvenance.FromRepo()),
            Node("concatenate", "Joining occupation configurations", ConcatenateFormula(),
                "append joins finite vectors in the displayed order. cast(size(p),i) transports i along N = left(p) + (a(p) + (b(p) + (d(p) + right(p)))). Thus no occupation is permuted.", AssessedProvenance.FromRepo()),
            Node("reducedState", "Tracing out the whole complement", ReducedStateFormula(),
                "The state on A, B and D is obtained from the outer product of the full vector by tracing over both components of E. Here star is the supplied scalar operation; the formula is defined over any semiring with a star operation and does not require normalization. For complex scalars it is the occupation-basis form of the source's reduced density matrix.", AssessedProvenance.FromLiterature(Source)),
            Node("occupation", "Particle number of a configuration", OccupationFormula(),
                "The total occupation is the natural sum of the zero-or-one occupations.", AssessedProvenance.FromRepo()),
            Node("spinTrace", "Ordinary spin partial trace", TraceFormula(false),
                "Section 3 defines the spin trace by summing the A,B,D matrix entries with the same B configuration on the bra and ket. The formula retains the source's order of the A and D indices and is defined over any semiring with a star operation.", AssessedProvenance.FromLiterature(Source)),
            Node("twistedTrace", "Partial trace with the B-parity insertion", TraceFormula(true),
                "Section 3 defines the parity-twisted trace as tr_B[(-1)ᴺᴮ ρ_ABD]. The factor is determined by the B occupation in the row; tracing identifies the row and column B labels. The scalar domain is any ring with a star operation. On D-parity-changing entries this is the fermionic trace in the source's factorization.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed extension to complex hopping", ClaimFormula(),
                "Theorem 1 gives coherence damping for ground states with real non-positive hopping. Section 7 asks whether it extends to complex hopping or frustrated lattices. The displayed proposition is the modulus version for all Hermitian complex single-particle matrices: every ground state, every adjacent partition, and every pair whose D occupations have different parity. Here mod denotes natural-number remainder (the Lean % operation). It does not impose the nonnegative-amplitude hypothesis behind the source's equality between an ordinary entry and its modulus.", AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("sokolovs-coherence-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A four-mode ground-state counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                ResultProse(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sokolovs-2026-complex-hopping-coherence-damping-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("sokolovs-coherence-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultProse() => Blocks(
        Paragraph(Text(
            "Take four ordered modes labelled 0,1,2,3 and the Hermitian matrix "
            + "h = (1/50)[[14, -9+16i, -48, -12-12i], [-9-16i, 14, -12+12i, -48], "
            + "[-48, -12-12i, -14, -16+9i], [-12+12i, -48, -16-9i, -14]]. "
            + "Let U = (1/√50)[[3,3,4,4], [3,-3,4,-4], [4,-4i,-3,3i], [4,4i,-3,-3i]]. "
            + "Then UU† = U†U = I and h = U† diag(-3/2,-1/2,1/2,3/2) U. "
            + "For cⱼ = annihilator(j), set dₖ = Σⱼ Uₖⱼ cⱼ. These are canonical fermionic modes.")),
        Paragraph(Text(
            "The normalized Slater state is "
            + "ψ = ((3c₀†+4c₂†)/5)((3c₁†+4c₃†)/5)|0000⟩ "
            + "= (9|1100⟩ + 12|1001⟩ - 12|0110⟩ + 16|0011⟩)/25. "
            + "It fills the two negative-energy modes, since the two occupied orbitals are "
            + "(d₀†+d₁†)/√2 and (d₀†-d₁†)/√2. Its squared norm is "
            + "(81+144+144+256)/625 = 1. Writing H = hamiltonian(h), the identity "
            + "H+2I = (3/2)d₀d₀† + (1/2)d₁d₁† + (1/2)d₂†d₂ + (3/2)d₃†d₃ "
            + "is a sum of positive semidefinite matrices. Each factor annihilates ψ: "
            + "d₀†ψ = d₁†ψ = d₂ψ = d₃ψ = 0. Hence Hψ = -2ψ and every normalized φ "
            + "has energy at least -2. This proves minimality on the entire Fock space.")),
        Paragraph(Text(
            "Choose A={0}, B={1}, D={2} and E={3}, so the five block lengths are (0,1,1,1,1). "
            + "For the A,D configurations x=(0,1) and y=(1,0), the D occupations have opposite parity. "
            + "After tracing out E, the B=0 contribution to this entry is 192/625 and the B=1 "
            + "contribution is -108/625. Thus spinTrace(p,ψ)(x,y) = 84/625, whereas "
            + "twistedTrace(p,ψ)(x,y) = 300/625 = 12/25. Both entries are real and positive, "
            + "and 12/25 > 84/625. The parity insertion reverses the negative contribution and "
            + "increases the coherence instead of damping it. This construction answers the complex-hopping "
            + "extension asked in Section 7; it does not contradict the real non-positive-hopping theorem.")));

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) => Seq(Parenthesized(left), Sp, F.Times, Sp, Parenthesized(right));
    private static Formula Tuple(params Formula[] values) => Parenthesized(Join(values));
    private static Formula Join(Formula[] values)
    {
        var items = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(values[i]);
        }
        return Seq([.. items]);
    }
    private static Formula SumOn(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Conj(Formula value) => Seq(Overline, Grp(value));
    private static Formula Adjoint(Formula value) => new Formula.Power(Parenthesized(value), Named("dagger"));
    private static Formula Nats => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Config(Formula n) => Call("Fock", n);
    private static Formula Mat(Formula indices, Formula scalars) => Call("Matrix", indices, indices, scalars);
    private static Formula Field(string name) => Call(name, V("p"));
    private static Formula Block(string name) => Config(Field(name));
    private static Formula Vector(Formula scalars) => Arrow(Config(V("N")), scalars);
    private static Formula AD => Product(Block("a"), Block("d"));
    private static Formula ABD => Product(Block("a"), Product(Block("b"), Block("d")));
    private static Formula First(Formula pair) => Call("fst", pair);
    private static Formula Second(Formula pair) => Call("snd", pair);
    private static Formula Number(Formula s) => Call("occupation", s);

    private static Formula FockFormula() => All("N", Nats,
        Eqn(Config(V("N")), Arrow(Fin(V("N")), Fin(D(2)))));

    private static Formula OperatorFormula() => All("N", Nats,
        Eqn(Call("Operator", V("N")), Mat(Config(V("N")), Complexes)));

    private static Formula AnnihilatorFormula()
    {
        var condition = And(Eqn(At(V("t"), V("j")), D(1)),
            Eqn(V("s"), Call("update", V("t"), V("j"), D(0))));
        var exponent = Seq(new Formula.Subscript(Sum,
            Seq(V("i"), Sp, Colon, Sp, Fin(V("N")), Comma, Sp, V("i"), Sp, Lt, Sp, V("j"))),
            Sp, Call("val", At(V("t"), V("i"))));
        var entry = Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
            new Formula.Power(Parenthesized(new Formula.Negate(D(1))), exponent), Sp, Named("else"), Sp, D(0));
        return All("N", Nats, All("j", Fin(V("N")), All("s", Config(V("N")),
            All("t", Config(V("N")), Eqn(Call("annihilator", V("j"), V("s"), V("t")), entry)))));
    }

    private static Formula HamiltonianFormula()
    {
        var product = Mul(Adjoint(Call("annihilator", V("j"))), Call("annihilator", V("k")));
        var summand = Mul(At(V("h"), V("j"), V("k")), Parenthesized(product));
        var sum = SumOn("j", Fin(V("N")), SumOn("k", Fin(V("N")), summand));
        return All("N", Nats, All("h", Mat(Fin(V("N")), Complexes),
            Eqn(Call("hamiltonian", V("h")), sum)));
    }

    private static Formula NormalizedFormula() => All("N", Nats, All("v", Vector(Complexes),
        IffOf(Call("Normalized", V("v")),
            Eqn(SumOn("s", Config(V("N")), Mul(Conj(At(V("v"), V("s"))), At(V("v"), V("s")))), D(1)))));

    private static Formula EnergyFormula()
    {
        var action = SumOn("t", Config(V("N")), Mul(At(V("H"), V("s"), V("t")), At(V("v"), V("t"))));
        var form = SumOn("s", Config(V("N")), Mul(Conj(At(V("v"), V("s"))), action));
        return All("N", Nats, All("H", Call("Operator", V("N")), All("v", Vector(Complexes),
            Eqn(Call("energy", V("H"), V("v")), At(Re, form)))));
    }

    private static Formula GroundStateFormula()
    {
        var comparison = Le(Call("energy", V("H"), V("v")), Call("energy", V("H"), V("w")));
        var minimal = All("w", Vector(Complexes), Imp(Call("Normalized", V("w")), comparison));
        return All("N", Nats, All("H", Call("Operator", V("N")), All("v", Vector(Complexes),
            IffOf(Call("IsGroundState", V("H"), V("v")), And(Call("Normalized", V("v")), minimal)))));
    }

    private static Formula PartitionFormula() => All("N", Nats,
        Eqn(Call("AdjacentPartition", V("N")), Seq(OpenBrace,
            Tuple(V("l"), V("a"), V("b"), V("d"), V("r")), Sp, Colon, Sp,
            new Formula.Power(Nats, D(5)), Sp, Mid, Sp,
            Eqn(V("N"), Add(V("l"), Parenthesized(Add(V("a"), Parenthesized(Add(V("b"), Parenthesized(Add(V("d"), V("r"))))))))), CloseBrace)));

    private static Formula ConcatenateFormula()
    {
        var joined = Call("append", V("l"), Call("append", V("a"),
            Call("append", V("b"), Call("append", V("d"), V("r")))));
        var entry = Eqn(Call("concatenate", V("p"), V("l"), V("a"), V("b"), V("d"), V("r"), V("i")),
            At(joined, Call("cast", Field("size"), V("i"))));
        var body = All("l", Block("left"), All("a", Block("a"), All("b", Block("b"),
            All("d", Block("d"), All("r", Block("right"), All("i", Fin(V("N")), entry))))));
        return PartitionParameters(body);
    }

    private static Formula PartitionParameters(Formula body) => All("N", Nats,
        All("p", Call("AdjacentPartition", V("N")), body));

    private static Formula ScalarParameters(bool ring, Formula body) => All("R", Named("Type"),
        Seq(OpenBracket, Call(ring ? "Ring" : "Semiring", V("R")), CloseBracket, Sp,
            OpenBracket, Call("Star", V("R")), CloseBracket, Comma, Sp, body));

    private static Formula ReducedStateFormula()
    {
        Formula Entry(Formula triple) => At(V("v"), Call("concatenate", V("p"), V("l"),
            First(triple), First(Second(triple)), Second(Second(triple)), V("r")));
        var entry = SumOn("l", Block("left"), SumOn("r", Block("right"),
            Mul(Entry(V("x")), Call("star", Entry(V("y"))))));
        var equation = Eqn(Call("reducedState", V("p"), V("v"), V("x"), V("y")), entry);
        return ScalarParameters(false, PartitionParameters(All("v", Vector(V("R")),
            All("x", ABD, All("y", ABD, equation)))));
    }

    private static Formula OccupationFormula() => All("N", Nats, All("s", Config(V("N")),
        Eqn(Number(V("s")), SumOn("i", Fin(V("N")), Call("val", At(V("s"), V("i")))))));

    private static Formula TraceFormula(bool twisted)
    {
        var entry = Call("reducedState", V("p"), V("v"),
            Tuple(First(V("x")), V("b"), Second(V("x"))),
            Tuple(First(V("y")), V("b"), Second(V("y"))));
        var summand = twisted ? Mul(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), Number(V("b"))), entry) : entry;
        return ScalarParameters(twisted, PartitionParameters(All("v", Vector(V("R")), All("x", AD, All("y", AD,
            Eqn(Call(twisted ? "twistedTrace" : "spinTrace", V("p"), V("v"), V("x"), V("y")),
                SumOn("b", Block("b"), summand)))))));
    }

    private static Formula ClaimFormula()
    {
        var parity = Ne(Call("mod", Number(Second(V("x"))), D(2)),
            Call("mod", Number(Second(V("y"))), D(2)));
        var inequality = Le(new Formula.Norm(Call("twistedTrace", V("p"), V("v"), V("x"), V("y"))),
            new Formula.Norm(Call("spinTrace", V("p"), V("v"), V("x"), V("y"))));
        var partitions = All("p", Call("AdjacentPartition", V("N")),
            All("x", AD, All("y", AD, Imp(parity, inequality))));
        return IffOf(Named("claim"), All("N", Nats, All("h", Mat(Fin(V("N")), Complexes),
            Imp(Eqn(Adjoint(V("h")), V("h")), All("v", Vector(Complexes),
                Imp(Call("IsGroundState", Call("hamiltonian", V("h")), V("v")), partitions))))));
    }
}
