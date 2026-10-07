using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class NandiMutualPredictabilityLOCCRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/nandi2025genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local measure-and-reset raises the mutually unbiased correlation I2 from 1 to 3/2, refuting its monotonicity under LOCC in the fixed and the optimized reading.",
        H("A local measure-and-reset refutes the LOCC monotonicity of I2"),
        Blocks(
            Node("setting", "A pair of local mutually unbiased bases", "Setting", SettingFormula(),
                "Alice's two bases are the columns of the unitary matrices A and A', Bob's those of B and B'; the bases of each party are mutually unbiased, |⟨a_i|a'_j⟩|² = 1/d, as in §II of arXiv:2509.24045v1 (\"{a', b'} ∈ B_2 which is mutually unbiased to B_1\").",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("product-vector", "The product basis vector", "prodVec", ProdVecFormula(),
                "The i-th column of X tensored with the i-th column of Y, so that ⟨i_a ⊗ i_b|ρ|i_a ⊗ i_b⟩ is the joint probability P_{a,b}(i,i) of Eq. (pAB).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("correlation", "The correlation I2 for a setting", "I2", I2Formula(),
                "I2 = C_{a,b} + C_{a',b'} with C_{a,b} = sum over i of P_{a,b}(i,i) (Eq. (cAB)); the expression is linear in ρ, so p_k I2(ρ_k) equals I2 of the unnormalized branch.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("optimized-correlation", "The optimized correlation", "I2max", I2maxFormula(),
                "The supremum of I2 over all local settings: the paper evaluates I2 of a pure state in its Schmidt basis, and this is the state-independent version of that choice.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("branch", "The unnormalized branch of a local instrument", "branch", BranchFormula(),
                "Eq. (10) uses ρ_k = (E_k ⊗ I) ρ (E_k ⊗ I)† / p_k; branch E ρ is the numerator, so p_k ρ_k = branch E_k ρ, including p_k = 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim-fixed", "Monotonicity for every fixed setting", "claimFixed", ClaimFixedFormula(),
                "The Conjecture of §II, \"The quantity I_2 is monotonically non-increasing under LOCC operations\", for the binary local instruments of Eq. (10), with I2 taken for any fixed pair of local mutually unbiased bases in any dimension d ≥ 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim-optimized", "Monotonicity of the optimized correlation", "claimOptimized", ClaimOptimizedFormula(),
                "The same inequality for the optimized correlation I2max in every dimension d ≥ 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture in either reading", "claim", ClaimFormula(),
                "The conjecture is read as the disjunction of the fixed and the optimized meaning of the quantity I2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture fails in both readings", "result", ResultFormula(),
                "Take d = 2, ρ = (1/2) I ⊗ |0⟩⟨0|, and Alice's instrument E₁ = |0⟩⟨0|, E₂ = |0⟩⟨1|, which measures and resets outcome 1 to |0⟩. Both branches equal (1/2)|00⟩⟨00|. For every setting I2 of ρ is 1, because each basis term is the sum over i of (1/2)|⟨b_i|0⟩|², which is 1/2 by unitarity of Bob's basis; hence I2max of ρ is 1. In the computational/Hadamard setting each branch has I2 = (1/2)(1 + 1/2) = 3/4, so the branches sum to 3/2 > 1, and the same lower bound holds for I2max.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nandi-2025-mub-correlation-locc-refutation"),
                    ResolutionKind.Refuted)
))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula C() => Seq(Mathbb, Grp(V("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, Formula arg) => Seq(head, Open, arg, Close);
    private static Formula App(Formula head, Formula first, Formula second) =>
        Seq(head, Open, first, Comma, Sp, second, Close);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Or(Formula left, Formula right) => Seq(left, Sp, Lor, Sp, right);
    private static Formula Not(Formula body) => Seq(Neg, Sp, body);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Leq2(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Plus2(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Times2(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula FinD(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", FinD(d), FinD(d), C());
    private static Formula PairIdx(Formula d) => Parenthesized(Times2(FinD(d), FinD(d)));
    private static Formula BigMat(Formula d) => Call("Matrix", PairIdx(d), PairIdx(d), C());
    private static Formula Dagger(Formula x) => Seq(x, Caret, Grp(V("H")));
    private static Formula Expect(Formula v, Formula rho) =>
        Call("re", Seq(Call("star", v), Sp, Cdot, Sp, Parenthesized(Seq(rho, Sp, Cdot, Sp, v))));
    private static Formula SumI(Formula body) =>
        Seq(Sum, Underscore, Grp(V("i")), Sp, body);

    private static Formula SettingFormula()
    {
        Formula d = V("d"), s = V("s"), i = V("i"), j = V("j");
        Formula unitary = And(Member(Call("A", s), Call("unitaryGroup", FinD(d), C())),
            And(Member(App(Seq(V("A"), Apos), s), Call("unitaryGroup", FinD(d), C())),
                And(Member(Call("B", s), Call("unitaryGroup", FinD(d), C())),
                    Member(App(Seq(V("B"), Apos), s), Call("unitaryGroup", FinD(d), C())))));
        Formula mubA = For(Seq(i, Sp, j), FinD(d), Equal(Call("normSq",
            App(Parenthesized(Times2(Dagger(Call("A", s)), App(Seq(V("A"), Apos), s))), i, j)), Seq(D(1), Slash, d)));
        Formula mubB = For(Seq(i, Sp, j), FinD(d), Equal(Call("normSq",
            App(Parenthesized(Times2(Dagger(Call("B", s)), App(Seq(V("B"), Apos), s))), i, j)), Seq(D(1), Slash, d)));
        return Disp(For(d, N(), For(s, Call("Setting", d),
            And(Parenthesized(unitary), And(Parenthesized(mubA), Parenthesized(mubB))))));
    }

    private static Formula ProdVecFormula()
    {
        Formula d = V("d"), x = V("X"), y = V("Y"), i = V("i"), a = V("a"), b = V("b");
        return Disp(For(d, N(), For(Seq(x, Sp, y), Mat(d), For(i, FinD(d), For(Seq(a, Sp, b), FinD(d),
            Equal(Call("prodVec", x, y, i, Parenthesized(Seq(a, Comma, Sp, b))),
                Times2(App(x, a, i), App(y, b, i))))))));
    }

    private static Formula I2Formula()
    {
        Formula d = V("d"), s = V("s"), rho = Rho, i = V("i");
        Formula first = SumI(Expect(Call("prodVec", Call("A", s), Call("B", s), i), rho));
        Formula second = SumI(Expect(Call("prodVec", App(Seq(V("A"), Apos), s), App(Seq(V("B"), Apos), s), i), rho));
        return Disp(For(d, N(), For(s, Call("Setting", d), For(rho, BigMat(d),
            Equal(Call("I2", s, rho), Plus2(first, second))))));
    }

    private static Formula I2maxFormula()
    {
        Formula d = V("d"), s = V("s"), rho = Rho;
        return Disp(For(d, N(), For(rho, BigMat(d), Equal(Call("I2max", rho),
            Seq(Operatorname, Grp(V("sup")), Underscore, Grp(Seq(s, Colon, Sp, Call("Setting", d))), Sp,
                Call("I2", s, rho))))));
    }

    private static Formula BranchFormula()
    {
        Formula d = V("d"), e = V("E"), rho = Rho;
        Formula kron = Call("kronecker", e, D(1));
        return Disp(For(d, N(), For(e, Mat(d), For(rho, BigMat(d),
            Equal(Call("branch", e, rho), Times2(Times2(kron, rho), Dagger(Parenthesized(kron))))))));
    }

    private static Formula Hypotheses(Formula d, Formula rho, Formula e1, Formula e2, Formula body) =>
        For(rho, BigMat(d), For(Seq(e1, Sp, e2), Mat(d),
            Imp(Call("PosSemidef", rho), Imp(Equal(Call("trace", rho), D(1)),
                Imp(Equal(Plus2(Times2(Dagger(e1), e1), Times2(Dagger(e2), e2)), D(1)), body)))));

    private static Formula ClaimFixedFormula()
    {
        Formula d = V("d"), s = V("s"), rho = Rho, e1 = V("E1"), e2 = V("E2");
        Formula ineq = Leq2(Plus2(Call("I2", s, Call("branch", e1, rho)), Call("I2", s, Call("branch", e2, rho))),
            Call("I2", s, rho));
        return Disp(IffOf(V("claimFixed"), Parenthesized(For(d, N(), Imp(Leq2(D(2), d),
            For(s, Call("Setting", d), Hypotheses(d, rho, e1, e2, ineq)))))));
    }

    private static Formula ClaimOptimizedFormula()
    {
        Formula d = V("d"), rho = Rho, e1 = V("E1"), e2 = V("E2");
        Formula ineq = Leq2(Plus2(Call("I2max", Call("branch", e1, rho)), Call("I2max", Call("branch", e2, rho))),
            Call("I2max", rho));
        return Disp(IffOf(V("claimOptimized"), Parenthesized(For(d, N(),
            Imp(Leq2(D(2), d), Hypotheses(d, rho, e1, e2, ineq))))));
    }

    private static Formula ClaimFormula() =>
        Disp(IffOf(V("claim"), Parenthesized(Or(V("claimFixed"), V("claimOptimized")))));

    private static Formula ResultFormula() => Disp(Not(V("claim")));
}
