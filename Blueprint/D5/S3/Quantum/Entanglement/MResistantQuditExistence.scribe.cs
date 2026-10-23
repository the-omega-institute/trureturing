using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class MResistantQuditExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/MResistantQuditExistence.";
    private static readonly LibraryNoteRef Quinta = LibraryNoteRef.Create("D5/L/QuantumBounds/quinta2019resistant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every N at least three and every m at most N minus two, a normalized pure state is entangled after every m-particle loss and fully separable after every (m+1)-particle loss.",
        H("M-resistant qudit states exist in every admissible range"),
        Blocks(
            Describe.Lean(DescribeId.Create("m-resistant-definition"), DeclarationHandle.Create(Prefix + "IsMResistant"),
                H("Resistance to particle loss"), StatementSource.FromAuthor(ResistantFormula()), AssessedProvenance.FromLiterature(Quinta),
                Blocks(Paragraph(Text("Quinta, Andre, Burchardt and Zyczkowski, arXiv:1908.10390v1, Section III, page 3: \"Definition: (m-resistance) An entangled state of N parties is called m-resistant if:\" \"It remains entangled as any m of its N subsystems are traced away;\" \"It becomes separable if a partial trace is performed over an arbitrary set of m + 1 subsystems.\" The initial entangled state gives the first conjunct. Separability means full separability, as in the later pure-state restatement. V labels sites and L labels a local basis; psi is the amplitude function. Both loss quantifiers range over every finite loss set J.")),
                    Paragraph(Text("The pure density uses D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity. Its implicit index type n is V -> L here; its amplitude argument precedes the row and column indices x and y. The outer product Matrix.vecMulVec psi (star psi) has entries:")),
                    new DocumentBlock.DisplayFormula(PureDensityFormula())), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("m-resistant-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The qudit existence conjecture"), StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Quinta),
                Blocks(Paragraph(Text("Quinta, Andre, Burchardt and Zyczkowski, arXiv:1908.10390v1, Section V, page 10: \"Conjecture 1. For any N and m, there exists an m-resistant N-qudit state in some local dimension d.\" Fin N replaces particle labels by 0,...,N-1 and Fin d labels a common local basis. Natural m is nonnegative. The whole admissible pure-state range is N >= 3 and m + 2 <= N: a remaining single particle cannot be entangled. Complex.normSq is the squared absolute value, so the finite sum fixes unit normalization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("m-resistant-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Existence by shared labels and localized bits"), StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(Quinta),
                Blocks(Paragraph(Text("Put k = N-m. Superpose the two bit branches of each k-element subset S. Every site records the common label S, while the branch bit is recorded only at sites in S. Tracing out m+1 sites meets every S and removes every off-diagonal entry; the diagonal marginal is a convex mixture of products of local basis projectors. After tracing out m sites, the kept k-element set supplies a surviving nonzero coherence. Exchanging one bit produces a zero diagonal, which the full-separability exchange theorem excludes. The same obstruction proves initial entanglement. The Lean construction embeds labels from Finset (Fin N) times Bool into Fin d by Fintype.equivFin; this full carrier has cardinality 2^(N+1), and only k-element labels occur in its support."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("quinta-andre-burchardt-zyczkowski-2019-m-resistant-states"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) => Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Config(Formula v, Formula l) => Arr(v, l);
    private static Formula Instances(string name, Formula body) => Seq(OpenBracket, Call("Fintype", F.Id(name)), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id(name)), CloseBracket, Comma, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula PureDensityFormula()
    {
        Formula n = F.Id("n"), psi = F.Id("psi"), x = F.Id("x"), y = F.Id("y");
        Formula owner = Seq(Operatorname, Grp(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot,
            F.Id("PureState"), Dot, F.Id("PureStateHandshake"), Dot, F.Id("rankOneDensity")));
        Formula entry = Eqn(Apply(owner, psi, x, y),
            new Formula.Binary(Apply(psi, x), FormulaBinaryOperator.Multiply, Call("star", Apply(psi, y))));
        return Disp(All("n", F.Id("Type"), All("psi", Arr(n, Complex()), All("x", n, All("y", n, entry)))));
    }
    private static Formula ResistantFormula()
    {
        Formula v = F.Id("V"), l = F.Id("L"), m = F.Id("m"), psi = F.Id("psi"), j = F.Id("J");
        Formula pure = Call("rankOneDensity", psi);
        Formula loss = All("J", Call("Finset", v), Imp(Eqn(Qualified("Finset", "card", j), m),
            new Formula.Not(Call("IsFullySeparableLocal", Call("partialTraceLocal", pure, j)))));
        Formula extra = All("J", Call("Finset", v), Imp(Eqn(Qualified("Finset", "card", j), Add(m, D(1))),
            Call("IsFullySeparableLocal", Call("partialTraceLocal", pure, j))));
        Formula body = And(new Formula.Not(Call("IsFullySeparableLocal", pure)), And(loss, extra));
        return Disp(All("V", F.Id("Type"), All("L", F.Id("Type"), Instances("V", Instances("L", All("m", Nat(),
            All("psi", Arr(Config(v, l), Complex()), IffTo(Call("IsMResistant", m, psi), body))))))));
    }
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), m = F.Id("m"), d = F.Id("d"), psi = F.Id("psi");
        Formula config = Config(Call("Fin", n), Call("Fin", d));
        Formula exists = Ex("d", Nat(), Ex("psi", Arr(config, Complex()),
            And(Eqn(SumOver("x", config, Qualified("Complex", "normSq", Apply(psi, F.Id("x")))), D(1)), Call("IsMResistant", m, psi))));
        Formula body = All("N", Nat(), All("m", Nat(), Imp(Leq(D(3), n), Imp(Leq(Add(m, D(2)), n), exists))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}
