using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FredkinEntanglingPowerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/qiu2025multipartite");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-qubit Fredkin gate F_4 generates more than two ebits across the cut AD:BC: one product input with auxiliary systems gives 2.00034... ebits. This refutes the conjecture of X. Qiu, Z. Song and L. Chen (arXiv:2410.15253) that the entanglement generation K_AD:BC(F_4) equals two ebits.",
        H("The four-qubit Fredkin gate generates more than two ebits across AD:BC"),
        Blocks(
            Node("party", "A party with its auxiliary system", PartyFormula(),
                "Each of the parties A, B, C and D is a qubit together with a local auxiliary system of dimension d, so its basis labels are pairs (q, r) with q in Fin 2 and r in Fin d.",
                "Party", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("swap", "The SWAP gate", SwapFormula(),
                "The SWAP gate S_2 on two qubits is the permutation matrix of the map (c, d) -> (d, c): its entry at row (c, d) and column (c', d') is 1 when (c', d') = (d, c) and 0 otherwise.",
                "swapGate", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gate", "The four-qubit Fredkin gate", GateFormula(),
                "The paper's gate F_4 = (|00><00| + |01><01| + |10><10|)_AB tensor I_CD + |11><11|_AB tensor (S_2)_CD on the qubit labels ((a, b), (c, d)). Here single(i, i, 1) is the matrix unit |i><i| and kronecker is the Kronecker product of matrices.",
                "fredkin4", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("output", "The output amplitudes", OutputFormula(),
                "The amplitudes of (F_4 tensor I_R)(psi_A tensor psi_B tensor psi_C tensor psi_D), indexed by the cut A R_A D R_D : B R_B C R_C. The label (((a, r_A), (d, r_D)), ((b, r_B), (c, r_C))) collects the qubits a, b, c, d and the auxiliary labels r_A, r_B, r_C, r_D; F_4 acts on the qubits and the identity acts on the auxiliary systems. The sum runs over all qubit labels ((s, t), (u, v)).",
                "output", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generated", "Entanglement generated from product inputs", GeneratedFormula(),
                "The values, in ebits, of the entanglement across A R_A D R_D : B R_B C R_C of an output of F_4: for auxiliary dimensions d_A, d_B, d_C, d_D, unit inputs psi_A, psi_B, psi_C, psi_D (the sum of the conjugate of psi_i times psi_i is 1), and the pure output state rho with entries output(i) times the conjugate of output(j), the von Neumann entropy -Tr(sigma log sigma) of the reduced state sigma = marginalRight(rho) on A R_A D R_D, divided by log 2. DensityState, vonNeumannEntropy and marginalRight are the existing definitions of density states (positive semidefinite matrices of trace 1), of the von Neumann entropy and of the partial trace over the right factor.",
                "generatedEntanglement", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generation", "The entanglement generation K_AD:BC(F_4)", GenerationFormula(),
                "The supremum of the generated entanglement over all auxiliary dimensions and all unit product inputs, as in the paper's definition of the multipartite entangling power for the fixed bipartition AD:BC.",
                "entanglementGeneration", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured value two ebits", ClaimFormula(),
                "The conjecture of the paper: the entanglement generation of F_4 across AD:BC is exactly two ebits. The paper proves that it lies between 2 and log_2 5.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "An input that generates more than two ebits",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take psi_A = (3|0> + 20|1>)/sqrt(409) and psi_B = sqrt(2/75)|0> + sqrt(73/75)|1> with one-dimensional auxiliary systems, and psi_C = psi_D = (|00> + |01> + |10> - |11>)/2 on a qubit and an auxiliary qubit. The output amplitude matrix M across the cut factors as D_A N D_B with D_A, D_B diagonal and N rational, so M M^* has the characteristic polynomial of the rational matrix N (D_B D_B^*) N^T (D_A^* D_A). A kernel-checked computation writes this matrix as P diag(mu) P^(-1) with rational P, so the reduced state has eigenvalues mu = (1752, 1460, 1460, 1460, 3, 0, 0, 0)/6135 and trace 1. The existing spectral lemmas turn the von Neumann entropy into the sum of -mu log mu over these eigenvalues. Writing each term through log(6135/(4k)) and bounding log(6135/5840) and log(6135/7008) by their Taylor polynomials with remainder, and log(6135/12) > 6 by e < 2.7182818286, gives an entropy above 2 log 2, that is 2.00034... > 2 ebits. The generated entanglement then contains a value above 2: if it is bounded above, its supremum exceeds 2; otherwise the supremum is 0. In either case K_AD:BC(F_4) is not 2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("qiu-2025-fredkin-entangling-power"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("fredkin-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, F.Times, Sp, right));
    private static Formula PartyOf(Formula d) => Call(F.Id("Party"), d);
    private static Formula Sub(Formula name, Formula index) => new Formula.Subscript(name, index);
    private static Formula PsiOf(string party) => Sub(Psi, F.Id(party));
    private static Formula DimOf(string party) => Sub(F.Id("d"), F.Id(party));
    private static Formula AuxOf(string party) => Sub(F.Id("r"), F.Id(party));
    private static Formula Single(byte i, byte j) =>
        Call(F.Id("single"), Pair(D(i), D(j)), Pair(D(i), D(j)), D(1));
    private static Formula Kron(Formula left, Formula right) => Call(F.Id("kronecker"), left, right);
    private static Formula OutputOf(Formula point) =>
        new Formula.Apply(Call(F.Id("output"), PsiOf("A"), PsiOf("B"), PsiOf("C"), PsiOf("D")),
            [point]);
    private static Formula AndAll(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula PartyFormula()
    {
        Formula d = F.Id("d");
        return Disp(Equal(PartyOf(d), Product(FinOf(D(2)), FinOf(d))));
    }

    private static Formula SwapFormula() =>
        Disp(Equal(F.Id("swapGate"), Call(F.Id("toMatrix"), Call(F.Id("toPEquiv"),
            Call(F.Id("prodComm"), FinOf(D(2)), FinOf(D(2)))))));

    private static Formula GateFormula()
    {
        Formula controlOff = Add(Add(Single(0, 0), Single(0, 1)), Single(1, 0));
        return Disp(Equal(F.Id("fredkin4"),
            Add(Kron(controlOff, D(1)), Kron(Single(1, 1), F.Id("swapGate")))));
    }

    private static Formula OutputFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula s = F.Id("s"), t = F.Id("t"), u = F.Id("u"), v = F.Id("v");
        Formula point = Pair(Pair(Pair(a, AuxOf("A")), Pair(d, AuxOf("D"))),
            Pair(Pair(b, AuxOf("B")), Pair(c, AuxOf("C"))));
        Formula qubits = Pair(Pair(s, t), Pair(u, v));
        Formula gateEntry = new Formula.Apply(F.Id("fredkin4"), [Pair(Pair(a, b), Pair(c, d)), qubits]);
        Formula amplitudes = Mul(Mul(Mul(
            new Formula.Apply(PsiOf("A"), [s, AuxOf("A")]),
            new Formula.Apply(PsiOf("B"), [t, AuxOf("B")])),
            new Formula.Apply(PsiOf("C"), [u, AuxOf("C")])),
            new Formula.Apply(PsiOf("D"), [v, AuxOf("D")]));
        Formula sum = Seq(new Formula.Subscript(Sum, qubits), Sp, Mul(gateEntry, amplitudes));
        return Disp(Equal(OutputOf(point), sum));
    }

    private static Formula GeneratedFormula()
    {
        Formula e = F.Id("E"), rho = Rho, i = F.Id("i"), j = F.Id("j");
        Formula dims = Seq(DimOf("A"), Comma, Sp, DimOf("B"), Comma, Sp, DimOf("C"), Comma, Sp,
            DimOf("D"));
        Formula inputType(string party) =>
            Seq(PsiOf(party), Sp, Colon, Sp, PartyOf(DimOf(party)), Sp, To, Sp, Complexes());
        Formula cutType = Product(Product(PartyOf(DimOf("A")), PartyOf(DimOf("D"))),
            Product(PartyOf(DimOf("B")), PartyOf(DimOf("C"))));
        Formula unit(string party) =>
            Equal(Call(F.Id("dotProduct"), Call(F.Id("star"), PsiOf(party)), PsiOf(party)), D(1));
        Formula pure = Seq(Forall, Sp, i, Sp, j, Comma, Sp,
            Equal(new Formula.Apply(rho, [i, j]),
                Mul(OutputOf(i), Call(F.Id("star"), OutputOf(j)))));
        Formula entropy = Equal(e, new Formula.Fraction(
            Call(F.Id("vonNeumannEntropy"), Call(F.Id("marginalRight"), rho)),
            Seq(Log, Sp, D(2))));
        Formula conditions = AndAll(unit("A"), unit("B"), unit("C"), unit("D"), pure, entropy);
        Formula body = Seq(Exists, Sp, dims, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Exists, Sp, inputType("A"), Comma, Sp, Exists, Sp, inputType("B"), Comma, Sp,
            Exists, Sp, inputType("C"), Comma, Sp, Exists, Sp, inputType("D"), Comma, Sp,
            Exists, Sp, rho, Sp, Colon, Sp, Call(F.Id("DensityState"), cutType), Comma, Sp,
            conditions);
        Formula set = Seq(OpenBrace, e, Sp, InMacro, Sp, Reals(), Sp, Mid, Sp, body, CloseBrace);
        return Disp(Equal(F.Id("generatedEntanglement"), set));
    }

    private static Formula GenerationFormula() =>
        Disp(Equal(F.Id("entanglementGeneration"),
            Call(F.Id("sSup"), F.Id("generatedEntanglement"))));

    private static Formula ClaimFormula() =>
        Disp(Iff(F.Id("claim"), Equal(F.Id("entanglementGeneration"), D(2))));
}
