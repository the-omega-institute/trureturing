using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class RendezvousVectorSystemGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/wang2026rendezvous");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative gap for symmetric rendezvous vector systems.",
        H("Rendezvous vector systems"), Blocks(
            Node("vertex", "Hypercube vertices", "Vertex",
                All("d", Naturals(), Equal(Local("Vertex", X("d")),
                    Call("Finset", Call("Fin", X("d"))))),
                "A vertex is a finite subset of Fin d, as in Wang's hypercube model in §2. WindowSeamCodes.Word is this finite-set type.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("output", "Fixed-cardinality outputs", "Output",
                Parameters(Equal(Local("Output", X("d"), X("t")),
                    Seq(OpenBrace, Typed(X("A"), Call("Finset", Call("Fin", X("d")))),
                        Sp, Slash, Slash, Sp, Equal(Card(X("A")), X("t")), CloseBrace))),
                "An output is a t-element subset of Fin d. Erdos7.CommonTreeUnion.Choice is the subtype with this cardinality equation. These are the output sets in §2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("wins", "The rendezvous condition", "Wins", WinsFormula(),
                "Equation (2.5) requires the two output sets to be disjoint and their union to equal the symmetric difference of the starting vertices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("n", "Number of outputs as a real number", "n",
                Parameters(Equal(Local("n", X("d"), X("t")),
                    CastReal(At(Qualified("Nat", "choose"), X("d"), X("t"))))),
                "The binomial coefficient counts the outputs. Its value here is cast from the natural numbers to the real numbers.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("kappa", "The quantitative gap", "kappa",
                Parameters(Equal(Local("kappa", X("d"), X("t")),
                    new Formula.Fraction(Num(1), Mul(
                        Power(Local("n", X("d"), X("t")), 4),
                        Power(Add(Mul(Mul(Num(4), At(Qualified("Real", "sqrt"), Num(2))),
                            CastReal(X("t"))), Num(2)), 2))))),
                "The gap depends on the number of outputs and the step length. It is positive whenever the number of outputs is positive.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("vector-system-gap", "A dimension-independent vector bound", "vector_system_gap",
                GapFormula(),
                "Consider a real vector space with a positive semidefinite inner-product core. The two vector families have unit pairing with h, squared lengths at most one, and a two-outcome squared-length bound for the first family. Every winning pair has pairing 1 − delta. For t at least two and d greater than twice t, delta is at least kappa. Exchange paths compare vectors leading to the same meeting vertex; a family of one more meeting vertices than outputs then forces the stated bound. This argument uses the rendezvous geometry of Wang's §2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static Formula WinsFormula() => Parameters(
        All("sigma", Vertex(), All("tau", Vertex(), All("A", Output(), All("B", Output(),
            IffOf(Local("Wins", X("sigma"), X("tau"), X("A"), X("B")),
                And(Call("Disjoint", Val(X("A")), Val(X("B"))),
                    Equal(Seq(Parenthesized(Val(X("A"))), Sp, Cup, Sp, Parenthesized(Val(X("B")))),
                        Call("symmDiff", X("sigma"), X("tau"))))))))));

    private static Formula GapFormula()
    {
        Formula ua = At(X("u"), X("sigma"), X("A"));
        Formula va = At(X("v"), X("tau"), X("B"));
        Formula uaPrime = At(X("u"), X("sigma"), X("Aprime"));
        Formula conclusion = LE(Local("kappa", X("d"), X("t")), X("delta"));
        Formula winning = All("sigma", Vertex(), All("tau", Vertex(), All("A", Output(),
            All("B", Output(), Imp(Local("Wins", X("sigma"), X("tau"), X("A"), X("B")),
                Equal(Inner(ua, va), Sub(Num(1), X("delta"))))))));
        Formula pairBound = All("sigma", Vertex(), All("A", Output(), All("Aprime", Output(),
            Imp(NE(X("A"), X("Aprime")), LE(Inner(Add(ua, uaPrime), Add(ua, uaPrime)), Num(2))))));
        Formula uNorm = All("sigma", Vertex(), All("A", Output(), LE(Inner(ua, ua), Num(1))));
        Formula vNorm = All("tau", Vertex(), All("B", Output(), LE(Inner(va, va), Num(1))));
        Formula uPairing = All("sigma", Vertex(), All("A", Output(), Equal(Inner(X("h"), ua), Num(1))));
        Formula vPairing = All("tau", Vertex(), All("B", Output(), Equal(Inner(X("h"), va), Num(1))));
        Formula assumptions = Imp(LE(Num(0), X("delta")), Imp(LE(X("delta"), Num(1)),
            Imp(Equal(Inner(X("h"), X("h")), Local("n", X("d"), X("t"))),
            Imp(uPairing, Imp(vPairing, Imp(uNorm, Imp(vNorm, Imp(pairBound, Imp(winning, conclusion)))))))));
        Formula vectors = Arrow(Vertex(), Arrow(Output(), X("V")));
        Formula body = Parameters(Imp(LE(Num(2), X("t")), Imp(LT(Mul(Num(2), X("t")), X("d")),
            All("h", X("V"), All("u", vectors, All("v", vectors, All("delta", Reals(), assumptions)))))));
        return All("V", Seq(X("Type"), Star),
            All("ag", Call("AddCommGroup", X("V")),
            All("module", Call("Module", Reals(), X("V")),
            All("C", At(Qualified("PreInnerProductSpace", "Core"), Reals(), X("V"),
                Qualified("Real", "instRCLike"), X("ag"), X("module")), body))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Local(string name, params Formula[] args) => At(Qualified("RendezvousVectorSystemGap", name), args);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Vertex() => Local("Vertex", X("d"));
    private static Formula Output() => Local("Output", X("d"), X("t"));
    private static Formula Val(Formula value) => At(Qualified("Subtype", "val"), value);
    private static Formula Card(Formula value) => At(Qualified("Finset", "card"), value);
    private static Formula Inner(Formula a, Formula b) => At(Qualified("Inner", "inner"),
        Reals(), X("V"), At(Seq(Operatorname,
            Grp(X("PreInnerProductSpace"), Dot, X("Core"), Dot, X("toInner"))),
            Reals(), X("V"), Qualified("Real", "instRCLike"), X("ag"), X("module"), X("C")), a, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Parameters(Formula body) => All("d", Naturals(), All("t", Naturals(), body));
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Power(Formula a, byte n) => new Formula.Power(Parenthesized(a), Num(n));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula NE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
