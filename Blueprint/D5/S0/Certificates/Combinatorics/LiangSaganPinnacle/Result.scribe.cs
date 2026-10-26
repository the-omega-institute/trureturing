using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics.LiangSaganPinnacle;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/liang2026distributivelattices");
    private const string Question = "Let σ be a permutation of distinct positive integers. Let Pin_n(σ) = {π ∈ S_n | the pinnacles of π are the elements of σ in that order}. … Computation of examples raise the following questions. Question 8.6. For all n and σ: (a) Is the restriction of the middle order to Pin_n(σ) a distributive lattice? (b) Is the sequence (pin_n(σ)) log-concave?";
    private const string Inversions = "Given π = π1 π2 . . . πn ∈ Sn in one-line notation, its set of inversion (values) is Inv π = {(πi, πj) | i < j and πi > πj}.";
    private const string InversionTop = "We also say that πi is an inversion top if (πi, πj) ∈ Inv π for some πj.";
    private const string IotaCoordinate = "where ιi = # of inversions in which i is an inversion top.";
    private const string Middle = "We can now use the bijection just given to define the middle order (Sn, ⪯) by π ⪯ σ if and only if ι(π) ≤ ι(σ) where the order on inversion tables is component-wise.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least six, an ordered pinnacle class contains two permutations without a common upper bound in the middle order.",
        H("Pinnacle fibres need not be lattices"), Blocks(
            Node("Peak", "An internal strict peak", All("n", N, All("p", Perm(V("n")), All("j", Fin(V("n")),
                Iff(Call("Peak", V("p"), V("j")), PeakBody(V("n"), V("p"), V("j")))))),
                "The predecessor and successor are actual positions in Fin n. Their index equations force 0<j<n−1, and both neighbouring values are strictly smaller.", DescribeRole.Definition),
            Node("pinnacleWord", "Pinnacles in positional order", All("n", N, All("p", Perm(V("n")),
                Eqn(Call("pinnacleWord", V("p")), Call("List.map", V("p"), Call("List.filter", Lam("j", Fin(V("n")), Call("decide", Call("Peak", V("p"), V("j")))), Call("List.finRange", V("n"))))))),
                "Question 8.6 defines pinnacles as values at internal positions with π(j−1)<π(j)>π(j+1), read from left to right. A permutation is the word π(0)π(1)…π(n−1); a Fin n value k represents the paper's positive value k+1. The increasing list of positions preserves the order of the pinnacle word.", DescribeRole.Definition, true),
            Node("iota", "The inversion-top table", All("n", N, All("p", Perm(V("n")), All("v", Fin(V("n")),
                Eqn(Call("iota", V("p"), V("v")), Call("Finset.card", Call("Finset.filter", Lam("w", Fin(V("n")), And(Lt(V("w"), V("v")), Lt(Pos(V("p"), V("v")), Pos(V("p"), V("w"))))), Call("Finset.univ"))))))),
                "Section 6, Permutations, printed pages 17–18: “" + Inversions + "” “" + InversionTop + "” Printed page 18: “" + IotaCoordinate + "” The paper's example 415632 has inversion table (0,0,1,3,2,2). Inverse positions count smaller values to the right of v, with no change of order direction.", DescribeRole.Definition, true),
            Node("middleLe", "The middle order", All("n", N, All("p", Perm(V("n")), All("q", Perm(V("n")),
                Iff(Call("middleLe", V("p"), V("q")), All("v", Fin(V("n")), Le(Call("iota", V("p"), V("v")), Call("iota", V("q"), V("v")))))))),
                "Section 6, Permutations, printed page 18: “" + Middle + "” The comparison is pointwise in the value, rather than in the position.", DescribeRole.Definition, true),
            Node("Pin", "The ordered pinnacle fibre", All("n", N, All("s", Call("List", Fin(V("n"))),
                Eqn(Call("Pin", V("n"), V("s")), Seq(OpenBrace, V("p"), Colon, Sp, Perm(V("n")), Sp, Mid, Sp, Eqn(Call("pinnacleWord", V("p")), V("s")), CloseBrace)))),
                "Section 8, printed pages 34–35, Question 8.6: “" + Question + "” A repeated value cannot occur in the pinnacle word of a permutation. A positive source value outside [n] gives an empty class; such a value has no Fin n encoding. The two values used below are distinct and lie in [n].", DescribeRole.Definition, true),
            Node("claim", "The universal distributive-lattice assertion", Eqn(V("claim"), Claim()),
                "Section 8, printed pages 34–35, Question 8.6: “" + Question + "” A distributive lattice is required to have exactly the order middleLe on the fibre. Requiring the assertion also for repeated Fin values introduces no counterexample here: the refutation uses the distinct ordered pair (n−2,n). Only part (a) is answered.", DescribeRole.Definition, true),
            Node("witness_peak", "Exactly two peak positions", KT(All("j", Fin(K6), Iff(Call("Peak", W(V("t")), V("j")), Or(Eqn(Val(V("j")), Add(V("t"), D(1))), Eqn(Val(V("j")), Add(V("t"), D(3))))))),
                "Write n=k+6 and t=0 or 1. The permutation witness k t has its two peaks at t+1 and t+3. For t=0 its word is 0,k+3,1,k+5,2,…,k+2,k+4. For t=1 its word is k+4,0,k+3,1,k+5,2,…,k+2. Explicit inverse functions prove that both words are permutations. Every other internal position is on an increasing run or next to a larger value."),
            Node("witness_word", "The common ordered pinnacle word", KT(Eqn(Call("pinnacleWord", W(V("t"))), Pair(FinValue(Add(V("k"), D(3))), FinValue(Add(V("k"), D(5)))))),
                "The two positions t+1 and t+3 occur in that order. Their values are k+3 and k+5, namely the source's n−2 and n. Filtering the increasing position list therefore yields precisely this ordered pair."),
            Node("iota_max", "Inversions of the maximum count positions to its right", All("n", N, All("p", Perm(V("n")), All("v", Fin(V("n")),
                Imp(Eqn(Add(Val(V("v")), D(1)), V("n")), Eqn(Call("iota", V("p"), V("v")), Sub(Sub(V("n"), D(1)), Val(Pos(V("p"), V("v"))))))))),
                "The inverse permutation bijects smaller values to the right of the maximum with all positions strictly after that maximum. The cardinality of this final Fin interval is n−1−pos(v)."),
            Node("witness_iota_max", "The maximum inversion count in the first word", All("k", N,
                Eqn(Call("iota", Call("witness", V("k"), D(0)), FinValue(Add(V("k"), D(5)))), Add(V("k"), D(2)))),
                "In the first word the maximum is at position 3, so its inversion count is k+2=n−4."),
            Node("witness_iota_second", "The saturated count in the second word", All("k", N,
                Eqn(Call("iota", Call("witness", V("k"), D(1)), FinValue(Add(V("k"), D(4)))), Add(V("k"), D(4)))),
                "The value k+4, the source's n−1, starts the second word. All k+4 smaller values are to its right, so its inversion count is k+4=n−2."),
            Node("word_positions", "The word determines the two peak positions", All("n", N, All("p", Perm(V("n")), All("a", Fin(V("n")), All("b", Fin(V("n")),
                Imp(Eqn(Call("pinnacleWord", V("p")), Pair(V("a"), V("b"))), And(Call("Peak", V("p"), Pos(V("p"), V("a"))), And(Call("Peak", V("p"), Pos(V("p"), V("b"))), Lt(Pos(V("p"), V("a")), Pos(V("p"), V("b")))))))))),
                "Applying the inverse permutation to the word recovers the filtered positions. Both are peaks, and the strict ordering of the original position list orders their inverse positions."),
            Node("obstruction", "Saturation excludes a common upper bound", All("k", N, All("u", Perm(K6),
                Imp(Eqn(Call("pinnacleWord", V("u")), Pair(FinValue(Add(V("k"), D(3))), FinValue(Add(V("k"), D(5))))),
                Imp(Call("middleLe", Call("witness", V("k"), D(0)), V("u")),
                Imp(Call("middleLe", Call("witness", V("k"), D(1)), V("u")), Call("False")))))),
                "Saturation forces k+4 before every smaller value, including the left neighbour of the first pinnacle k+3. That pinnacle has position at least 2. Its right neighbour is smaller, so the larger pinnacle k+5 cannot occupy the next position; its position is at least 4. Its inversion count is at most k+1, whereas dominance of the first word requires at least k+2."),
            Node("sigma", "The pinnacle word for the family", All("n", N, All("h", Le(D(6), V("n")),
                Eqn(Call("sigma", V("n"), V("h")), Pair(FinValue(Sub(V("n"), D(3))), FinValue(Sub(V("n"), D(1))))))),
                "These Fin n values encode the positive values (n−2,n). They are distinct for every n≥6.", DescribeRole.Definition),
            Node("no_common_upper_bound", "A non-lattice fibre for every n at least six", Family(),
                "Set k=n−6. The two explicit permutations have the required ordered pinnacle word. The preceding position argument excludes every common upper bound in that same fibre. Thus every n≥6 has an ordered pinnacle class which is not even a lattice."),
            Describe.Lean(DescribeId.Create("liang-sagan-result"), DeclarationHandle.Create(Prefix + "result"), H("A negative answer to Question 8.6(a)"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At n=6 the two permutations are 142635 and 514263 in positive values, with pinnacle word (4,6). A distributive-lattice join would be an upper bound of both, contrary to the general family theorem. Question 8.6(b), concerning log-concavity of the class sizes, remains unanswered here."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("liang-sagan-2026-pinnacle-middle-order"), ResolutionKind.Refuted)) )));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create("liang-sagan-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula N => Call("Nat");
    private static Formula K6 => Add(V("k"), D(6));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula App(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula FinValue(Formula n) => Seq(Langle, Sp, n, Rangle, Sp);
    private static Formula Perm(Formula n) => Call("Equiv.Perm", Fin(n));
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Pos(Formula p, Formula v) => App(Call("Equiv.symm", p), v);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(V(name), Colon, Sp, type, Mapsto, Sp, body);
    private static Formula Pair(Formula a, Formula b) => Seq(OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula W(Formula t) => Call("witness", V("k"), t, V("h"));
    private static Formula KT(Formula body) => All("k", N, All("t", N, All("h", Le(V("t"), D(1)), body)));
    private static Formula PeakBody(Formula n, Formula p, Formula j) => Ex("l", Fin(n), Ex("r", Fin(n),
        And(Eqn(Add(Val(V("l")), D(1)), Val(j)), And(Eqn(Add(Val(j), D(1)), Val(V("r"))), And(Lt(App(p,V("l")),App(p,j)),Lt(App(p,V("r")),App(p,j)))))));
    private static Formula Claim() => All("n", N, All("s", Call("List", Fin(V("n"))),
        Ex("L", Call("DistribLattice", Call("Pin", V("n"), V("s"))), All("x", Call("Pin", V("n"), V("s")), All("y", Call("Pin", V("n"), V("s")),
            Iff(new Formula.Apply(Seq(V("L"), Dot, V("le")), [V("x"), V("y")]), Call("middleLe", Call("Subtype.val", V("x")), Call("Subtype.val", V("y")))))))));
    private static Formula Family() => All("n", N, All("h", Le(D(6), V("n")),
        Ex("A", Call("Pin", V("n"), Call("sigma", V("n"), V("h"))), Ex("B", Call("Pin", V("n"), Call("sigma", V("n"), V("h"))),
        All("U", Call("Pin", V("n"), Call("sigma", V("n"), V("h"))), new Formula.Not(And(Call("middleLe", Call("Subtype.val", V("A")), Call("Subtype.val", V("U"))), Call("middleLe", Call("Subtype.val", V("B")), Call("Subtype.val", V("U"))))))))));
}
