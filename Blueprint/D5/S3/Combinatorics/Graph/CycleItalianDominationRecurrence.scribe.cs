using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CycleItalianDominationRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/shao2026italiandomination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total number of Italian dominating functions on the labelled cycle C_n, for n at least three, satisfies a constant-coefficient recurrence of order five. Its first five values are 23, 60, 167, 467 and 1297. A bijection with closed sequences in a nine-state transfer matrix identifies the count with a power trace; a five-state factorization then supplies the recurrence.",
        H("Italian dominating functions on cycles"),
        Blocks(
            Node("italian", "The Italian condition", ItalianFormula(),
                "Shao and Zhao, Definition 2.1 (p. 5): \"An Italian dominating function (IDF) on G = (V, E) is a function f : V → {0, 1, 2} such that for every v ∈ V with f(v) = 0, Σ_{u∈N(v)} f(u) ≥ 2. The weight of f is ω(f) = Σ_{v∈V} f(v).\" The vertices are labelled by Fin n and the values by Fin 3. Write r_n = finRotate n; its inverse and itself are the cyclic predecessor and successor. For n ≥ 3 these are distinct and form exactly the open neighbourhood in SimpleGraph.cycleGraph n, so the displayed sum is the neighbourhood sum of Definition 2.1. For n < 3 the definition is a cyclic-word condition; no simple-cycle interpretation is asserted. The operator val takes a Fin 3 value to its natural-number value.",
                "IsItalian", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The total count", CountFormula(),
                "Shao and Zhao, Definition 1.1 (p. 3): \"where d_I(G, k) counts the Italian dominating functions of weight k.\" For n ≥ 3, a(n) is therefore Σ_k d_I(C_n, k): all labelled maps satisfying the Italian condition are counted once, without identifying rotations or reflections. In the displayed expression, univ is the finite set of all maps of the indicated type, filter selects those satisfying IsItalian, and card is the Finset cardinality. Section 2.1 (p. 5) states: \"A cycle graph C_n (n ≥ 3) has vertices v_1, v_2, …, v_n and edges v_i v_{i+1} for i = 1, …, n − 1 plus the edge v_n v_1.\" Labelling i by v_{i+1} gives the cycle used here.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The recurrence and its initial values", Disp(Iff(F.Id("claim"), ClaimBody())),
                "Shao and Zhao, §9 (the section starts on p. 28; this bullet is on p. 29): \"Several directions remain open for future work: … • Deriving a complete linear recurrence for the total count Σ_k d_I(C_n, k) using the transfer matrix formulation (the observed limiting ratio ≈ 2.7843 is the dominant eigenvalue of the corresponding transfer matrix).\" The displayed proposition gives a recurrence for every n ≥ 3 and the five initial values that determine all subsequent terms. Every count in the recurrence is explicitly coerced from the natural numbers to the integers, so subtraction is integer subtraction; the initial equalities are in the natural numbers. The order here describes the supplied recurrence; minimality is not asserted by this proposition.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "A complete order-five recurrence", Disp(ClaimBody()),
                "Use pair states (a,b) in {0,1,2}². A transition from (a,b) to (b,c) is allowed exactly when b ≠ 0 or a+c ≥ 2. Mapping f to the sequence of pairs (f at the predecessor of i, f at i), and decoding the second coordinates, gives mutually inverse maps between Italian functions and closed state sequences. An induction expands a matrix power as a sum of path products; closing the paths gives the trace. The transition rows agree in the five groups {(0,0)}, {(1,0)}, {(2,0)}, {(*,1)}, {(*,2)}. Their indicator matrix R and representative-row matrix S satisfy T = R S and S R = Q, with Q having rows (0,0,0,0,1), (0,0,0,1,1), (1,0,0,1,1), (0,1,0,1,1), (0,0,1,1,1). Cyclicity of trace gives a(n) = trace(Q^n) for positive n. The identity Q^5 − 2Q^4 − 2Q^3 − Q^2 + Q + I = 0, multiplied by Q^n and traced, yields the recurrence. The traces of Q^3 through Q^7 give the five initial values.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shao-zhao-2026-cycle-italian-domination-recurrence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("italian-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula MapType(Formula n) => Seq(Fin(n), Sp, To, Sp, Fin(D(3)));
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(variable), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Twice(Formula value) =>
        new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, value);
    private static Formula A(Formula n) => Call("a", n);
    private static Formula CastA(Formula n) => Parenthesized(Seq(A(n), Sp, Colon, Sp, Int));

    private static Formula ItalianFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), i = F.Id("i");
        Formula rotate = Call("finRotate", n);
        Formula predecessor = new Formula.Apply(
            new Formula.Power(Parenthesized(rotate), Seq(Minus, D(1))), [i]);
        Formula successor = new Formula.Apply(rotate, [i]);
        Formula at = new Formula.Apply(f, [i]);
        Formula prev = Call("val", new Formula.Apply(f, [predecessor]));
        Formula next = Call("val", new Formula.Apply(f, [successor]));
        Formula condition = All("i", Fin(n),
            Logic(EqTo(at, D(0)), FormulaLogicOperator.Implies, LeTo(D(2), Add(prev, next))));
        return Disp(All("n", Nat, All("f", MapType(n),
            Iff(Call("IsItalian", n, f), condition))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f");
        Formula maps = new Formula.Subscript(Call("univ"), Parenthesized(MapType(n)));
        Formula predicate = Seq(Parenthesized(Seq(f, Sp, Colon, Sp, MapType(n))), Sp, Mapsto, Sp,
            Call("IsItalian", n, f));
        return Disp(All("n", Nat, EqTo(A(n), Call("card", Call("filter", maps, predicate)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula positive = Add(Add(Twice(CastA(Add(n, D(4)))),
            Twice(CastA(Add(n, D(3))))), CastA(Add(n, D(2))));
        Formula rhs = Sub(Sub(positive, CastA(Add(n, D(1)))), CastA(n));
        Formula recurrence = All("n", Nat,
            Logic(LeTo(D(3), n), FormulaLogicOperator.Implies,
                EqTo(CastA(Add(n, D(5))), rhs)));
        return And(recurrence, And(EqTo(A(D(3)), D(2,3)),
            And(EqTo(A(D(4)), D(6,0)), And(EqTo(A(D(5)), D(1,6,7)),
            And(EqTo(A(D(6)), D(4,6,7)), EqTo(A(D(7)), D(1,2,9,7)))))));
    }
}
