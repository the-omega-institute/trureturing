using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RootDeltaFineRingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/RootDeltaFineRings.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/danchev2026rootdeltafine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every root-Delta-fine associative unital ring is fine, including the trivial ring.",
        H("A negative answer to displayed Problem 4.4 of sqrt(Delta)-Fine Rings"),
        Blocks(
            Node("delta-member", "The explicit left-unit test", "DeltaMember",
                DeltaDefinition(), DescribeRole.Definition,
                "In arXiv:2608.30734v2, Introduction S1.p6, Delta consists exactly of d for "
                    + "which 1-v*d is a unit for every two-sided unit v. Units(R) denotes Lean's "
                    + "R-units and val(v) its value in R. The multiplication order is essential.", true),
            Node("root-delta-member", "A strictly positive power in Delta", "RootDeltaMember",
                RootDefinition(), DescribeRole.Definition,
                "Introduction S1.p7 requires an exponent at least one. The witness n is a "
                    + "natural number and 0<n is an explicit conjunct.", true),
            Node("root-delta-fine", "Root-Delta-fine rings", "RootDeltaFine",
                DecompositionDefinition("RootDeltaFine", "RootDeltaMember"), DescribeRole.Definition,
                "Definition 2.1 quantifies over every nonzero r. Its decomposition has a "
                    + "two-sided unit and a root-Delta summand. No commutation is imposed; "
                    + "only the source's separately named strong variant imposes that condition.", true),
            Node("fine-ring", "Fine rings", "Fine",
                DecompositionDefinition("Fine", "IsNilpotent"), DescribeRole.Definition,
                "Introduction S1.p4 requires the same decomposition for every nonzero element, "
                    + "with a nilpotent summand. IsNilpotent is Mathlib's standard power-zero predicate.", true),
            Node("zero-delta", "Zero belongs to Delta", "zero_delta",
                Context(Call("DeltaMember", D(0))), DescribeRole.Theorem,
                "Every test at zero is the unit one. This also proves the reverse containment "
                    + "needed to read delta_eq_zero as Delta={0}."),
            Node("delta-not-unit", "A Delta member cannot be a unit in a nontrivial ring", "delta_not_unit",
                Context(Implies(Call("Nontrivial", F.Id("R")),
                    All("d", F.Id("R"), Implies(Call("DeltaMember", F.Id("d")),
                        new Formula.Not(Call("IsUnit", F.Id("d"))))))), DescribeRole.Theorem,
                "For a unit d, its inverse makes 1-d inverse*d equal to zero. Nontriviality "
                    + "is needed only by this auxiliary statement, not by the main theorems."),
            Node("delta-equals-zero", "Root-Delta-fineness forces Delta to be zero", "delta_eq_zero",
                Context(Implies(Call("RootDeltaFine", F.Id("R")),
                    All("d", F.Id("R"), Implies(Call("DeltaMember", F.Id("d")),
                        Equal(F.Id("d"), D(0)))))), DescribeRole.Theorem,
                "Apply the decomposition to a hypothetical nonzero Delta member d=u+a. "
                    + "The test b=1-u inverse*d is a unit. The proof checks (-u)*b=a using "
                    + "associativity, distributivity and u*u inverse=1 in this order. Thus a "
                    + "and the power witnessing its root-Delta membership are units, a contradiction. "
                    + "Nontriviality is constructed locally from d not equal to zero; the theorem "
                    + "itself assumes only Ring(R) and RootDeltaFine(R)."),
            Node("root-delta-implies-fine", "Every root-Delta-fine ring is fine", "rootDeltaFine_implies_fine",
                Context(Implies(Call("RootDeltaFine", F.Id("R")), Call("Fine", F.Id("R")))),
                DescribeRole.Theorem,
                "The positive power of each summand belongs to Delta and is therefore zero. "
                    + "The same unit and summand give a fine decomposition. This answers the "
                    + "entire displayed Problem 4.4 negatively for arbitrary associative unital rings, "
                    + "with no commutativity, finiteness or nontriviality hypothesis."),
            Node("fine-implies-root-delta", "Every fine ring is root-Delta-fine", "fine_implies_rootDeltaFine",
                Context(Implies(Call("Fine", F.Id("R")), Call("RootDeltaFine", F.Id("R")))),
                DescribeRole.Theorem,
                "A nilpotency exponent n gives the strictly positive exponent n+1. Its power "
                    + "is zero, which belongs to Delta. This handles Mathlib's exponent-zero "
                    + "convention without excluding the trivial ring."),
            Node("root-delta-iff-fine", "The two ring classes coincide", "rootDeltaFine_iff_fine",
                Context(Iff(Call("RootDeltaFine", F.Id("R")), Call("Fine", F.Id("R")))),
                DescribeRole.Theorem,
                "The checked forward and converse implications give an equivalence in every "
                    + "carrier universe. In these displays Type denotes Type u for arbitrary u, "
                    + "and Ring(R) renders Lean's typeclass binder [Ring R]."),
            Node("no-root-delta-counterexample", "Displayed Problem 4.4: No", "no_rootDeltaFine_not_fine",
                Context(new Formula.Not(And(Call("RootDeltaFine", F.Id("R")),
                    new Formula.Not(Call("Fine", F.Id("R")))))), DescribeRole.Theorem,
                "Danchev, Hasanzadeh, Moussavi and Javan ask: Is there a sqrt(Delta)-fine ring "
                    + "which is not fine? The answer is No. The pre-question paragraph conjectures "
                    + "existence, while the concluding discussion conjectures the implication; "
                    + "the introductory radical-description prose is also inconsistent. This "
                    + "result follows the explicit unit-test definitions and the displayed question, "
                    + "without relying on those other assertions. Global prior publication and "
                    + "priority remain ASSUMED-UNVERIFIED; no first-discovery claim is made."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, DescribeRole role, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create("root-delta-fine-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula DeltaDefinition()
    {
        var r = F.Id("R");
        var d = F.Id("d");
        var v = F.Id("v");
        return Context(All("d", r, Iff(Call("DeltaMember", d),
            All("v", Call("Units", r), Call("IsUnit",
                new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
                    new Formula.Binary(Call("val", v), FormulaBinaryOperator.Multiply, d)))))));
    }

    private static Formula RootDefinition()
    {
        var a = F.Id("a");
        var n = F.Id("n");
        return Context(All("a", F.Id("R"), Iff(Call("RootDeltaMember", a),
            ExistsOne("n", Call("Nat"), And(Seq(D(0), Sp, Lt, Sp, n),
                Call("DeltaMember", new Formula.Power(a, n)))))));
    }

    private static Formula DecompositionDefinition(string name, string summandPredicate)
    {
        var r = F.Id("R");
        var x = F.Id("x");
        var v = F.Id("v");
        var a = F.Id("a");
        var decomposition = ExistsOne("v", Call("Units", r), ExistsOne("a", r,
            And(Equal(x, new Formula.Binary(Call("val", v), FormulaBinaryOperator.Add, a)),
                Call(summandPredicate, a))));
        return Context(Iff(Call(name, r), All("x", r,
            Implies(new Formula.Not(Equal(x, D(0))), decomposition))));
    }

    private static Formula Context(Formula body) => Disp(All("R", Call("Type"),
        Implies(Call("Ring", F.Id("R")), body)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsOne(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
}
