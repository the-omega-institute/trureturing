using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QutritRankOneMicOrthogonalPairsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/debrota2020varieties");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine positive semidefinite rank-one effects on C^3 sum to the identity and span every Hermitian matrix over the reals. Nine distinct unordered pairs have zero trace product. This refutes Conjecture 1 of DeBrota, Fuchs and Stacey, arXiv:1812.08762v5, which allows at most seven such pairs. The effects have unequal traces.",
        H("A rank-one qutrit MIC with nine orthogonal pairs"),
        Blocks(
            Node("mic", "Rank-one minimal informational completeness", MicFormula(),
                "The source defines a POVM (printed page 1): \"Let ℋ_d be a d-dimensional complex Hilbert space, and let {E_i} be a set of positive semidefinite operators on that space which sum to the identity: ∑_(i=1)^N E_i = I.\" \"The set {E_i} is a positive-operator-valued measure (POVM), which is the mathematical representation of a measurement process in quantum theory.\" It then says (printed pages 1-2): \"A POVM is said to be informationally complete (IC) if the operators {E_i} span ℒ(ℋ_d), the space of Hermitian operators on ℋ_d, and an IC POVM is said to be minimal if it contains exactly d² elements.\" Here d = 3, the index type is Fin 9, and each effect has Matrix.rank = 1. The span is over R: every Hermitian H is a real linear combination of the effects, and the effects themselves are Hermitian. Thus the span is exactly the Hermitian space. There is no condition that the traces are equal.",
                "IsRankOneMIC", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pairs", "Unordered orthogonal pairs", PairsFormula(),
                "The paper defines the Gram matrix by \"[G]_{ij} := tr E_i E_j\" (printed page 2). Its seven-pair example counts distinct unordered pairs. We represent each pair once by (a,b) with a < b in Fin 9; diagonal pairs are excluded. Orthogonality is the complex equality tr(E(a) E(b)) = 0. No real-part test replaces it.",
                "orthogonalPairs", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "\"A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements.\" (Conjecture 1, printed page 6, arXiv:1812.08762v5.) E ranges over all families of nine complex 3 by 3 matrices satisfying IsRankOneMIC. The pairs are counted once by increasing indices. The preceding example (printed page 5) says \"When multiplied by 1/3, the following is a rank-1 unbiased MIC in dimension 3 with 7 orthogonal pairs.\" The conjecture itself says rank-1 MIC and imposes no unbiasedness condition.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Nine pairs refute the seven-pair bound", Disp(new Formula.Not(F.Id("claim"))),
                "Let v = [(1,i,-1), (1,-1,1+i), (1-i,0,-1), (1,-1+i,1+i), (0,1,i), (-1-i,i,1), (1,1,1), (1,i,-1-i), (1,-i,0)] and k = [3,2,2,4,3,3,9,7,11], with indices 0 through 8. The effects E(a) = (k(a)/46) v(a) v(a)^* are positive semidefinite; each outer product has rank at most one and a nonzero diagonal entry establishes rank at least one. Their sum is I. For x = [Re H00, Re H11, Re H22, Re H01, Im H01, Re H02, Im H02, Re H12, Im H12], define c(a) = (Jx)(a)/k(a), where J is the integer matrix 46 times the inverse of the coordinate matrix of the outer products. Expanding gives H = ∑_a c(a) E(a) for every Hermitian H. The nine pairs (0,1), (0,8), (1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,8) have zero trace product. Their cardinality is nine, so the total number is at least nine and cannot be at most seven. The traces are 9/46, 4/23, 3/23, 10/23, 3/23, 6/23, 27/46, 14/23, 11/23; this example is biased.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debrota-2020-rank-one-mic-seven-orthogonal-pairs-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("qutritmic-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula FinNine() => Call("Fin", D(9));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Matrices() => Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(D(3), Times, Sp, D(3)));
    private static Formula Family() => Seq(FinNine(), Sp, To, Sp, Matrices());
    private static Formula Apply(Formula function, Formula arg) => new Formula.Apply(function, [arg]);
    private static Formula SumOver(Formula index, Formula term) => Seq(new Formula.Subscript(Sum, index), Sp, term);

    private static Formula MicFormula()
    {
        Formula e = F.Id("E"), a = F.Id("a"), h = F.Id("H"), c = F.Id("c");
        Formula ea = Apply(e, a);
        Formula psd = All("a", FinNine(), Call("PosSemidef", ea));
        Formula sum = Equal(SumOver(a, ea), D(1));
        Formula rank = All("a", FinNine(), Equal(Call("rank", ea), D(1)));
        Formula herm = All("a", FinNine(), Call("IsHermitian", ea));
        Formula reconstruction = Equal(h, SumOver(a,
            Seq(Apply(c, a), Sp, Cdot, Sp, ea)));
        Formula span = All("H", Matrices(), Implies(Call("IsHermitian", h),
            Some("c", Seq(FinNine(), Sp, To, Sp, Reals()), reconstruction)));
        return Disp(All("E", Family(), Iff(Call("IsRankOneMIC", e), And(psd, And(sum, And(rank, And(herm, span)))))));
    }

    private static Formula PairsFormula()
    {
        Formula e = F.Id("E"), a = F.Id("a"), b = F.Id("b");
        Formula pair = Parenthesized(Seq(a, Comma, Sp, b));
        Formula domain = Seq(FinNine(), Times, Sp, FinNine());
        Formula less = new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
        Formula product = Seq(Apply(e, a), Sp, Apply(e, b));
        Formula zero = Equal(Call("trace", product), D(0));
        Formula set = Seq(OpenBrace, Sp, pair, Sp, InMacro, Sp, domain, Sp, Mid, Sp,
            And(less, zero), Sp, CloseBrace);
        return Disp(All("E", Family(), Equal(Call("orthogonalPairs", e), set)));
    }

    private static Formula ClaimFormula()
    {
        Formula e = F.Id("E");
        Formula bound = new Formula.Relation(Call("card", Call("orthogonalPairs", e)),
            FormulaRelationOperator.LessThanOrEqual, D(7));
        return Disp(Iff(F.Id("claim"), All("E", Family(), Implies(Call("IsRankOneMIC", e), bound))));
    }
}
