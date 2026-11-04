using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class PeriodicSshExcessPseudoEntropyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/khareletal2026pseudoentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-phase half-filled ground states of a periodic three-cell SSH chain have positive averaged excess pseudo-entropy.",
        H("Positive excess pseudo-entropy in a periodic SSH chain"), Blocks(
            Paragraph(Text(
                "The modes are ordered (1,A), (1,B), …, (N,A), (N,B), with zero-based indices in Fin(2N). "
                    + "An occupation configuration is a function Fin(2N) → Bool, where true means occupied. "
                    + "JordanWigner denotes D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner, "
                    + "and FockMajoranaCarrier denotes D5.S3.Quantum.Fermionic.FockMajoranaCarrier. "
                    + "Their annihilation and number operators act on the full occupation space. "
                    + "All finite-type sums range over the displayed type. Nat.div and Nat.mod are natural quotient and remainder. "
                    + "Matrix.conjTranspose is conjugate transpose; star conjugates a vector pointwise, "
                    + "dotProduct is the bilinear coordinate sum, Matrix.mulVec is matrix action, and SMul.smul is scalar multiplication. "
                    + "Casts display their target type. Type* allows any universe; bracketed Fintype and DecidableEq assumptions are anonymous instances.")),
            Node("sshHopping", "The periodic single-particle hopping matrix", HoppingFormula(),
                "The intracell bond joins the A and B modes of each cell with real amplitude v. "
                    + "The intercell bond has amplitude w = 1 and joins each B orbital to the A orbital of the next cell. "
                    + "The remainder modulo 2N includes the bond from (N,B) to (1,A), in both directions, as in equation (15).",
                AssessedProvenance.FromRepo(Source)),
            Node("hamiltonian", "The many-body SSH Hamiltonian", HamiltonianFormula(),
                "Equation (15) acts on the full fermionic Fock space by the sum of hopping coefficients times cᵢ†cⱼ. "
                    + "JordanWigner.fullC uses the stated ordering of the modes, so the annihilator at j has the parity string from all earlier modes. "
                    + "The periodic bond is included in the same operator sum, with these fermionic signs.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("periodic-ssh-excess-fullc-mixed"),
                DeclarationHandle.Create(Prefix + "fullC_mixed"),
                H("The mixed canonical anticommutation relation"),
                StatementSource.FromAuthor(Disp(MixedCarFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The anticommutator of an annihilator and a creator is the identity for equal modes and zero for distinct modes."))),
                DescribeRole.Theorem),
            Node("IsHalfFilledGroundState", "Half filling and ground-state minimality", GroundStateFormula(),
                "Half filling means exactly N particles among the 2N modes. The vector is nonzero and is an eigenvector "
                    + "of FockMajoranaCarrier.numberOperator with eigenvalue N. Its energy is minimal among all nonzero "
                    + "vectors in that particle sector. The inequality is the comparison of Rayleigh quotients after "
                    + "multiplication by the two positive squared norms, so no normalization is required.",
                AssessedProvenance.FromRepo(Source)),
            Node("reduce", "Partial trace over the later cells", ReductionFormula(),
                "Subsystem A consists of the first L cells, hence the first 2L modes in the Jordan–Wigner order. "
                    + "Fin.castLE embeds these initial indices into Fin(2N). The two full configurations agree on "
                    + "every later orbital and restrict to a and b on the initial modes. Summing their matrix entries "
                    + "traces out the modes of the remaining cells. This initial partition crosses no modes.",
                AssessedProvenance.FromRepo(Source)),
            Node("matrixEntropy", "Spectral entropy with algebraic multiplicity", EntropyFormula(),
                "The characteristic roots are taken with algebraic multiplicity. The multiset is mapped by z ↦ −z log z "
                    + "and then summed. Complex.log is the principal scalar logarithm, with Complex.log(0) = 0. "
                    + "This is the spectral form of equations (1)–(3), agreeing with −Tr(X log X) wherever that matrix function is defined.",
                AssessedProvenance.FromRepo(Source)),
            Node("averagedExcess", "The averaged excess pseudo-entropy", ExcessFormula(),
                "Matrix.vecMulVec forms the outer product. The first reduced matrix is the transition "
                    + "ψ₁ψ₂† divided by the overlap ψ₂†ψ₁. The other two are the normalized pure-state density matrices. "
                    + "Equation (21) subtracts the mean of the two input entropies from the real part of the transition entropy. "
                    + "The definition takes real parts of all three spectral entropies; for reduced density matrices their entropies are real.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "Non-positivity for every same-phase periodic chain", ClaimFormula(),
                "Section IV asserts non-positivity for same-phase half-filled SSH ground states at w = 1, "
                    + "and Section VI states that periodic boundary conditions give no exceptions at any system size. "
                    + "Here 1 ≤ L < N makes A a nonempty proper initial segment of cells. "
                    + "Both couplings have absolute value below one, or both have absolute value above one. "
                    + "The assertion includes every pair of half-filled ground states with nonzero overlap, "
                    + "and retains both the topological and the trivial phase.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("periodic-ssh-excess-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Positive excess for three unit cells"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take three unit cells, A the first cell, v₁ = 3/8 and v₂ = 5/8. Both couplings are in the topological phase. "
                            + "Write an occupation configuration as the integer k = ∑ⱼ₌₀⁵ 2ʲ xⱼ, with xⱼ = 1 for an occupied orbital. "
                            + "Two rational ground states have the following pairs of amplitudes at their nonzero coordinates: "
                            + "7:(−4,−2), 11:(20,6), 13:(−20,−6), 14:(4,2), 19:(−20,−6), 21:(21,7), "
                            + "22:(−5,−3), 25:(−5,−3), 26:(5,3), 28:(−4,−2), 35:(4,2), 37:(−5,−3), "
                            + "38:(5,3), 41:(5,3), 42:(−21,−7), 44:(20,6), 49:(−4,−2), 50:(20,6), "
                            + "52:(−20,−6), 56:(4,2); every other amplitude is zero. "
                            + "Each occupied configuration has three particles. The squared norms are 3528 and 392, "
                            + "the overlap is 1152, and the ground energies are −25/8 and −27/8, respectively.")),
                    Paragraph(Text(
                        "In the occupation basis 00, 10, 01, 11 of the first cell, each reduced matrix has diagonal "
                            + "entries (a,p,p,a), entries q at positions (10,01) and (01,10), and zero elsewhere. "
                            + "For the normalized transition, (a,p,q) = (2/9,5/18,−1/6), "
                            + "with spectrum {2/9,2/9,4/9,1/9}. For the first reduced density matrix, "
                            + "(a,p,q) = (104/441,233/882,−5/42), with spectrum {104/441,104/441,169/441,64/441}. "
                            + "For the second, (a,p,q) = (10/49,29/98,−3/14), with spectrum {10/49,10/49,25/49,4/49}. "
                            + "All three spectra are strictly positive. Their entropies are, respectively, "
                            + "2 log 3 − (4/3) log 2; 2 log 3 + 2 log 7 − (16/7) log 2 − (26/21) log 13; "
                            + "and 2 log 7 − (4/7) log 2 − (10/7) log 5.")),
                    Paragraph(Text(
                        "Consequently ∆S = (1/21) log(2²·3²¹·5¹⁵·13¹³/7⁴²) > 0. "
                            + "The sign follows from the integer inequality 7⁴² < 2²·3²¹·5¹⁵·13¹³. "
                            + "Thus non-positivity fails for a one-cell subsystem even when both periodic-chain ground states are in the same phase."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kharel-limbu-khatri-khanal-adhikari-2026-periodic-ssh-excess-pseudo-entropy"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("periodic-ssh-excess-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(N(part)));
        }
        return Seq([.. items]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Typed(N(name), type), Mapsto, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, type)), Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Q("if"), Sp, Parenthesized(condition), Sp, Q("then"), Sp, yes, Sp, Q("else"), Sp, no);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Occupations(Formula n) => new Formula.TypeArrow(FinOf(n), N("Bool"));
    private static Formula Vector(Formula n) => new Formula.TypeArrow(Parenthesized(Occupations(n)), N("Complex"));
    private static Formula MatrixOf(Formula index, Formula scalar) => Call("Matrix", index, index, scalar);
    private static Formula Operator(Formula n) => MatrixOf(Parenthesized(Occupations(n)), N("Complex"));
    private static Formula Twice(Formula n) => Mul(D(2), n);
    private static Formula TwoN() => Twice(N("N"));
    private static Formula TwoL() => Twice(N("L"));
    private static Formula SizeBinders(Formula body) => All("N", N("Nat"), All("L", N("Nat"),
        All("h", Le(TwoL(), TwoN()), body)));
    private static Formula StateBinders(Formula body) => All("psi1", Vector(TwoN()),
        All("psi2", Vector(TwoN()), body));
    private static Formula StarOf(Formula x) => Call("star", x);
    private static Formula Inner(Formula x, Formula y) => Call("dotProduct", StarOf(x), y);
    private static Formula RealPart(Formula x) => Call("Complex.re", x);
    private static Formula NumberAction(Formula x) => Call("Matrix.mulVec",
        Call("FockMajoranaCarrier.numberOperator", TwoN()), x);
    private static Formula HalfFilling(Formula x) => Eq(NumberAction(x),
        Call("SMul.smul", Typed(N("N"), N("Complex")), x));
    private static Formula Energy(Formula x) => RealPart(Inner(x,
        Call("Matrix.mulVec", Call("hamiltonian", N("N"), N("v")), x)));
    private static Formula NormSquared(Formula x) => RealPart(Inner(x, x));

    private static Formula HoppingFormula()
    {
        var i = N("i");
        var j = N("j");
        var iv = Call("Fin.val", i);
        var jv = Call("Fin.val", j);
        var intracell = And(Eq(Call("Nat.div", iv, D(2)), Call("Nat.div", jv, D(2))), Ne(i, j));
        var forward = And(Eq(Call("Nat.mod", iv, D(2)), D(1)),
            Eq(jv, Call("Nat.mod", Add(iv, D(1)), TwoN())));
        var backward = And(Eq(Call("Nat.mod", jv, D(2)), D(1)),
            Eq(iv, Call("Nat.mod", Add(jv, D(1)), TwoN())));
        return All("N", N("Nat"), All("v", N("Real"), Eq(
            Typed(Call("sshHopping", N("N"), N("v")), MatrixOf(FinOf(TwoN()), N("Real"))),
            Lambda("i", FinOf(TwoN()), Lambda("j", FinOf(TwoN()),
                Add(Parenthesized(If(intracell, N("v"), D(0))),
                    Parenthesized(If(Or(forward, backward), D(1), D(0)))))))));
    }

    private static Formula HamiltonianFormula() => All("N", N("Nat"), All("v", N("Real"),
        Eq(Typed(Call("hamiltonian", N("N"), N("v")), Operator(TwoN())),
            SumOver("i", FinOf(TwoN()), SumOver("j", FinOf(TwoN()), Call("SMul.smul",
                Typed(Typed(Call("sshHopping", N("N"), N("v"), N("i"), N("j")), N("Real")), N("Complex")),
                Mul(Call("Matrix.conjTranspose", Call("JordanWigner.fullC", N("i"))),
                    Call("JordanWigner.fullC", N("j")))))))));

    private static Formula MixedCarFormula()
    {
        var ci = Call("JordanWigner.fullC", N("i"));
        var cj = Call("Matrix.conjTranspose", Call("JordanWigner.fullC", N("j")));
        return All("M", N("Nat"), All("i", FinOf(N("M")), All("j", FinOf(N("M")),
            Eq(Add(Mul(ci, cj), Mul(cj, ci)),
                If(Eq(N("i"), N("j")), Typed(D(1), Operator(N("M"))), D(0))))));
    }

    private static Formula GroundStateFormula() => All("N", N("Nat"), All("v", N("Real"),
        All("psi", Vector(TwoN()), IffFormula(Call("IsHalfFilledGroundState", N("N"), N("v"), N("psi")),
            And(Ne(N("psi"), D(0)), And(HalfFilling(N("psi")),
                All("phi", Vector(TwoN()), Imp(Ne(N("phi"), D(0)), Imp(HalfFilling(N("phi")),
                    Le(Mul(Energy(N("psi")), NormSquared(N("phi"))),
                        Mul(Energy(N("phi")), NormSquared(N("psi")))))))))))));

    private static Formula ReductionFormula()
    {
        var initialX = All("i", FinOf(TwoL()), Eq(At(N("x"), Call("Fin.castLE", N("h"), N("i"))), At(N("a"), N("i"))));
        var initialY = All("i", FinOf(TwoL()), Eq(At(N("y"), Call("Fin.castLE", N("h"), N("i"))), At(N("b"), N("i"))));
        var later = All("k", FinOf(TwoN()), Imp(Le(TwoL(), Call("Fin.val", N("k"))),
            Eq(At(N("x"), N("k")), At(N("y"), N("k")))));
        return SizeBinders(All("X", Operator(TwoN()), Eq(Typed(Call("reduce", N("h"), N("X")), Operator(TwoL())),
            Lambda("a", Occupations(TwoL()), Lambda("b", Occupations(TwoL()),
                SumOver("x", Occupations(TwoN()), SumOver("y", Occupations(TwoN()),
                    If(And(initialX, And(initialY, later)), At(N("X"), N("x"), N("y")), D(0)))))))));
    }

    private static Formula EntropyFormula() => All("n", Seq(N("Type"), Star),
        Instance(Call("Fintype", N("n")), Instance(Call("DecidableEq", N("n")),
            All("X", MatrixOf(N("n"), N("Complex")), Eq(Typed(Call("matrixEntropy", N("X")), N("Complex")),
                Call("Multiset.sum", Call("Multiset.map",
                    Lambda("z", N("Complex"), new Formula.Negate(Mul(N("z"), Call("Complex.log", N("z"))))),
                    Call("Polynomial.roots", Call("Matrix.charpoly", N("X"))))))))));

    private static Formula ReducedEntropy(Formula left, Formula right) => RealPart(Call("matrixEntropy",
        Call("reduce", N("h"), Call("SMul.smul", Call("Inv.inv", Inner(right, left)),
            Call("Matrix.vecMulVec", left, StarOf(right))))));

    private static Formula ExcessFormula() => SizeBinders(StateBinders(
        Eq(Typed(Call("averagedExcess", N("h"), N("psi1"), N("psi2")), N("Real")),
            Sub(ReducedEntropy(N("psi1"), N("psi2")), new Formula.Fraction(
                Add(ReducedEntropy(N("psi1"), N("psi1")), ReducedEntropy(N("psi2"), N("psi2"))), D(2))))));

    private static Formula ClaimFormula() => IffFormula(N("claim"), SizeBinders(
        Imp(Le(D(1), N("L")), Imp(Lt(N("L"), N("N")),
            All("v1", N("Real"), All("v2", N("Real"),
                Imp(Or(And(Lt(new Formula.Absolute(N("v1")), D(1)), Lt(new Formula.Absolute(N("v2")), D(1))),
                    And(Lt(D(1), new Formula.Absolute(N("v1"))), Lt(D(1), new Formula.Absolute(N("v2"))))),
                    StateBinders(Imp(Call("IsHalfFilledGroundState", N("N"), N("v1"), N("psi1")),
                        Imp(Call("IsHalfFilledGroundState", N("N"), N("v2"), N("psi2")),
                            Imp(Ne(Inner(N("psi2"), N("psi1")), D(0)),
                                Le(Call("averagedExcess", N("h"), N("psi1"), N("psi2")), D(0)))))))))))));
}
