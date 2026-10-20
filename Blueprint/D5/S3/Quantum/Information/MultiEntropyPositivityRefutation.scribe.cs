using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class MultiEntropyPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/gaddejainkrishnakulkarnisharma2024multientropy");
    private const string PositivityQuote = "Section 7, printed p. 32: \"The definition (1.11) of S_n requires that the quantity E_n be positive definite. In this paper, we did not prove or even discuss this and phrased the monotonicity conjecture in terms of E_n instead. Although we found that E_n is positive in the examples we studied, it would be nice to prove this in general and to see if there is any relation between the positivity of E_n and the coarse-graining monotonicity.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth replica invariant of the antisymmetric three-qutrit state is -35/58773123072, so the replica invariant need not be positive on normalized pure states.",
        H("Multi-entropy positivity fails on three qutrits"),
        Blocks(
            Node("E", "Replica invariant", InvariantFormula(),
                "Section 1.2, printed pp. 6–7, equations (1.10)–(1.11): \"Consider m = n^{q−1} replicas, arranged as a q−1 dimensional regular hyper-cubical lattice.\" and \"The permutation σ_q is taken to be identity and the rest of the permutations are taken to be the generators of independent Z_n symmetries i.e. σ_a = g_a for a = 1, …, q − 1.\". The local basis at party a is L(a). Replicas are functions Fin(q - 1) to ZMod(n); shift is StabilizerMultiEntropyCollapse.shift. With zero-based party labels, shift translates coordinate a when a < q - 1 and leaves the last party fixed. star is complex conjugation. The finite sums and products include every basis assignment and every replica exactly once. Type universes are implicit.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("IsUnitState", "Normalized pure state", UnitStateFormula(),
                "A normalized pure-state amplitude has sum of squared absolute values one over all joint basis indices. Complex.normSq is the squared absolute value. The local basis at party a is L(a), and each L(a) is finite. Type universes are implicit.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "Positivity question", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                PositivityQuote + " Footnote 2 states: \"Note that in defining the Renyi multi-entropy S_n in equation (1.11), we have tacitly assumed that the quantity E_n^(q) is positive.\" The formula quantifies over n and q at least two, every finite local basis and every complex pure-state amplitude with sum of squared absolute values one. Positive means positive real part and zero imaginary part. The NeZero argument and the family of Fintype arguments are anonymous instance parameters.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "A negative fourth replica invariant", new Formula.Not(Parenthesized(ClaimBody())),
                "At n = 4 and q = 3 take L(a) = Fin 3 and the totally antisymmetric state with coefficients epsilon(i,j,k)/sqrt(6). The determinant of the matrix whose rows select i, j and k gives epsilon. Its six nonzero coefficients have squared modulus 1/6. Summing the unshifted third party gives the two-party kernel (I - F)/6, where F exchanges the two qutrits. Reindexing the replica lattice turns the contraction into the trace of the fourth power of its row transfer, divided by 6^16. The integer trace is -1680, giving E(4,3,psi) = -35/58773123072. This contradicts the positive-real-part conclusion. The coarse-graining inequalities formulated directly for E retain their separate statements.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gadde-jain-krishna-kulkarni-sharma-2023-multi-entropy-positivity"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("gjk-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(name.Split('.').SelectMany((part, index) =>
        index == 0 ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula PiType(string name, Formula domain, Formula codomain) =>
        Arrow(Parenthesized(Seq(F.Id(name), Colon, Sp, domain)), codomain);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(Formula q, Formula l) => PiType("a", Call("Fin", q), At(l, F.Id("a")));
    private static Formula Replicas(Formula n, Formula q) =>
        Arrow(Call("Fin", Subtract(q, D(1))), Call("ZMod", n));
    private static Formula FiniteLocals(Formula q, Formula l) => All("a", Call("Fin", q), Call("Fintype", At(l, F.Id("a"))));
    private static Formula SumOver(string name, Formula type, Formula value) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, value);
    private static Formula ProductOver(string name, Formula type, Formula value) =>
        Seq(Prod, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, value);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));

    private static Formula InvariantFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), l = F.Id("L"), psi = F.Id("psi"), x = F.Id("x"), r = F.Id("r"), a = F.Id("a");
        Formula shifted = Fun("a", Call("Fin", q), At(x, Call("shift", n, q, a, r), a));
        Formula term = Multiply(Call("star", At(psi, At(x, r))), At(psi, shifted));
        Formula rhs = SumOver("x", Arrow(Parenthesized(Replicas(n, q)), Parenthesized(Local(q, l))),
            ProductOver("r", Replicas(n, q), term));
        return All("n", NatType(), All("q", NatType(), Instance(Call("NeZero", n),
            All("L", Arrow(Call("Fin", q), F.Id("Type")), Instance(FiniteLocals(q, l),
                All("psi", Arrow(Parenthesized(Local(q, l)), ComplexType()), Equal(Call("E", n, q, psi), rhs)))))));
    }

    private static Formula UnitStateFormula()
    {
        Formula q = F.Id("q"), l = F.Id("L"), psi = F.Id("psi"), x = F.Id("x");
        Formula normalized = Equal(SumOver("x", Local(q, l), Call("Complex.normSq", At(psi, x))), D(1));
        return All("q", NatType(), All("L", Arrow(Call("Fin", q), F.Id("Type")),
            Instance(FiniteLocals(q, l), All("psi", Arrow(Parenthesized(Local(q, l)), ComplexType()),
                Equal(Call("IsUnitState", psi), Parenthesized(normalized))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), q = F.Id("q"), l = F.Id("L"), psi = F.Id("psi");
        Formula normalized = Call("IsUnitState", psi);
        Formula invariant = Call("E", n, q, psi);
        Formula conclusion = Both(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("Complex.re", invariant)),
            Equal(Call("Complex.im", invariant), D(0)));
        return All("n", NatType(), All("q", NatType(), Instance(Call("NeZero", n),
            ImpliesTo(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n),
                ImpliesTo(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, q),
                    All("L", Arrow(Call("Fin", q), F.Id("Type")), Instance(FiniteLocals(q, l),
                        All("psi", Arrow(Parenthesized(Local(q, l)), ComplexType()), ImpliesTo(normalized, conclusion)))))))));
    }
}
