using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TwoQubitBinegativityMonotonicityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.";
    private static readonly LibraryNoteRef Girard =
        LibraryNoteRef.Create("D5/L/QuantumStates/girard2017binegativity");
    private static readonly LibraryNoteRef Sazim =
        LibraryNoteRef.Create("D5/L/QuantumStates/sazim2018binegativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binegativity increases under a finite one-way LOCC channel on two qubits. Alice applies a local filter and sends its outcome to Bob, who resets to |1> on failure. Forgetting the outcomes gives a deterministic counterexample to the monotonicity conjecture of Girard and Gour.",
        H("Binegativity is not monotone under one-way LOCC"),
        Blocks(
            Node("channel", "Finite one-way LOCC channels", ChannelFormula(),
                "Alice has n outcomes with Kraus matrices A(i). On receiving outcome i, Bob applies the channel with m(i) Kraus matrices B(i,j). Both completeness equalities are required. The outcomes are forgotten, so E is the double Kraus sum. The tensor product is Matrix.kronecker, and adjoint is conjugate transpose. The finite Kraus representation permits zero Kraus matrices and includes channels with different numbers of Kraus matrices for different Alice outcomes.",
                "IsOneWayLOCC", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("claim", "The monotonicity conjecture", ClaimFormula(),
                "Girard and Gour, arXiv:1701.02724v3, p. 1, introduction: \"That is, we conjecture that for any two-qubit state σ it holds that N₂(ℰ(σ)) ≤ N₂(σ) for any LOCC (or PPT) channel ℰ that outputs states of two qubits.\" Sazim and Awasthi, arXiv:1711.03717v2, p. 1, introduction: \"On the basis of numerical evidence, it is conjectured that the binegativity behaves monotonically under both LOCC and PPT channels [15].\" Their abstract, p. 1, also says: \"Our study supports the conjecture that the binegativity is a monotone.\" The encoding quantifies over matrices on Fin 2 times Fin 2, with IsDensity meaning positive semidefinite and trace one, and over every E satisfying IsOneWayLOCC. This restricted universal assertion is implied by the quoted LOCC assertion. Binegativity is the existing N_2(sigma) = ReTr[(sigma^Gamma)_-] + 2 ReTr[(((sigma^Gamma)_-)^Gamma)_-], with partial transposition on Bob's qubit and Mathlib's negative part. ReTr agrees with trace on these self-adjoint matrices. The output again has two qubits.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Sazim)),
            Describe.Example(DescribeId.Create("tqbm-restatement"),
                H("The independent restatement"), Disp(F.Id("claim")),
                AssessedProvenance.FromLiterature(Sazim),
                Blocks(Paragraph(Text("Sazim and Awasthi, arXiv:1711.03717v2, p. 1: \"On the basis of numerical evidence, it is conjectured that the binegativity behaves monotonically under both LOCC and PPT channels [15].\" The statement above uses finite one-way LOCC channels, a subclass of LOCC.")))),
            Node("result", "The conjecture fails", Disp(new Formula.Not(F.Id("claim"))),
                "The input in the basis 00,01,10,11 is rho = (3/4)|00><00| + (1/8)(|01>+|10>)(<01|+<10|). Alice uses diag(1/2,1) and (sqrt(3)/2)|0><0|. Bob does nothing on outcome 0 and resets to |1> on outcome 1. The output matrix has entries rho'(00,00)=3/16, rho'(01,01)=11/16, rho'(10,10)=1/8 and rho'(01,10)=rho'(10,01)=1/16, with every other entry zero. Positive semidefinite rank-one decompositions with zero positive-negative product identify both successive negative parts. Their traces give N_2(rho) = -1/4 + 7 sqrt(10)/80 and N_2(rho') = -1/32 + 7 sqrt(13)/416. The rational certificates sqrt(10) < 31623/10000 and sqrt(13) > 36055/10000 show a strict increase. The input is a density matrix and each conditional local Kraus family is complete, so this is a deterministic one-way LOCC counterexample.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Girard),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girard-2017-binegativity-monotonicity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("tqbm-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula EqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula NumberSet(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Qubit() => Call("Matrix", Fin(D(2)), Fin(D(2)), NumberSet("C"));
    private static Formula PairType() => Seq(Fin(D(2)), Sp, F.Times, Sp, Fin(D(2)));
    private static Formula State() => Call("Matrix", Parenthesized(PairType()), Parenthesized(PairType()), NumberSet("C"));
    private static Formula Function(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SumOver(Formula i, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(i, Sp, Colon, Sp, type)), Sp, body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Adj(Formula a) => Call("conjTranspose", a);
    private static Formula Tensor(Formula a, Formula b) => Call("kronecker", a, b);

    private static Formula ChannelFormula()
    {
        Formula e = F.Id("E"), n = F.Id("n"), m = F.Id("m"),
            a = F.Id("A"), b = F.Id("B"), i = F.Id("i"), j = F.Id("j"), sigma = F.Id("sigma");
        Formula ai = Apply(a, i), bij = Apply(b, i, j), mi = Apply(m, i);
        Formula bobType = Seq(Parenthesized(Seq(i, Colon, Sp, Fin(n))), Sp, To, Sp, Function(Fin(mi), Qubit()));
        Formula alice = EqTo(SumOver(i, Fin(n), Mul(Adj(ai), ai)), D(1));
        Formula bob = All(i, Fin(n), EqTo(SumOver(j, Fin(mi), Mul(Adj(bij), bij)), D(1)));
        Formula k = Tensor(ai, bij);
        Formula action = All(sigma, State(), EqTo(Apply(e, sigma),
            SumOver(i, Fin(n), SumOver(j, Fin(mi), Mul(Mul(k, sigma), Adj(k))))));
        Formula condition = Some(n, NumberSet("N"), Some(m, Function(Fin(n), NumberSet("N")),
            Some(a, Function(Fin(n), Qubit()), Some(b, bobType, And(alice, And(bob, action))))));
        return Disp(All(e, Function(State(), State()), Logic(Call("IsOneWayLOCC", e), FormulaLogicOperator.Iff, condition)));
    }

    private static Formula ClaimFormula()
    {
        Formula sigma = F.Id("sigma"), e = F.Id("E");
        Formula inequality = Rel(Call("binegativity", Apply(e, sigma)),
            FormulaRelationOperator.LessThanOrEqual, Call("binegativity", sigma));
        Formula body = All(sigma, State(), Imp(Call("IsDensity", sigma),
            All(e, Function(State(), State()), Imp(Call("IsOneWayLOCC", e), inequality))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, body));
    }
}
