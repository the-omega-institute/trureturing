using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class StationaryOccupationResidualStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single repeated unitary attains the product-minus-maximum occupation memory dimension.",
        H("Stationary Occupation Memory Attainment"),
        Blocks(
            Paragraph(Text(
                "A is an arbitrary finite nonempty alphabet with decidable equality and a is "
                + "an arbitrary multiset on A. Let d(a) be the product over i:A of count(a,i)+1, "
                + "minus the maximum count. The dimension is a natural number. Space(I) and "
                + "Unitary(I) are the actual complex Euclidean space and its linear isometry "
                + "equivalences. Word(A,n) is Fin(n) to A, and L(a)=card(a).")),
            Paragraph(Text(
                "Choose a head q of maximum capacity. A nonzero-tail memory index records "
                + "the remaining tail occupation and a head index h. Emitting q decrements "
                + "h, with the h=0 coefficient zero. Emitting a tail letter with at least "
                + "two remaining tail letters decrements that tail coordinate and preserves "
                + "h. With exactly one tail letter remaining, only h=0 can emit it, and "
                + "the transition enters the sink.")),
            Describe.Lean(DescribeId.Create("positive-residual-transitions"),
                DeclarationHandle.Create(Prefix + "positive_residual_step"),
                H("Every legal positive-tail transition has the prescribed residual"),
                StatementSource.FromAuthor(Disp(Context(All("a", Multi,
                    PositiveTransitions())))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "PositiveResidualStep(a) means: for every b<=a with positive tail count, "
                    + "every i belonging to b, and every k:Fin(d(a)), the (i,k) coefficient "
                    + "of physicalGate(a) applied to a fresh q and physicalResidual(a,b) "
                    + "equals physicalResidual(a,erase(b,i))(k). The head case uses a "
                    + "successor reindexing of the finite sum. The two tail cases use the "
                    + "multiplicity square-root identities and the sink boundary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stationary-dimension-attained"),
                DeclarationHandle.Create(Prefix + "stationary_memory_dimension_attained"),
                H("The exact proposed dimension is attained by one fixed gate"),
                StatementSource.FromAuthor(Disp(Attainment)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "C(U,L,0,J(blank,L,x),w,k) is the (w,k) coefficient of the actual "
                        + "L-slot circuit with the literal constant schedule U, acting on "
                        + "all slots initialized to blank and memory x. The same U and "
                        + "blank are used at every step. sector(L,a,w) equals the positive "
                        + "inverse square root of the number of occupation-a words on "
                        + "those words, and zero on all other words.")),
                    Paragraph(Text(
                        "The residual transitions imply every word coefficient by induction. "
                        + "The normalized sector and the unitary circuit imply that the "
                        + "initial vector, the complex inverse square root of multiplicity(card(a),a) times physicalResidual(a,a), has norm one. The common final memory "
                        + "is the sink basis vector. This includes zero occupation and "
                        + "letters of zero capacity; all physical memory is Fin(d(a))."))), DescribeRole.Theorem))));

    private static Formula PositiveTransitions()
    {
        var b = Id("b");
        var i = Id("i");
        var q = Call("maximalHead", a);
        var hypotheses = And(new Formula.Relation(b, FormulaRelationOperator.LessThanOrEqual, a),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("tailCount", q, b)));
        var output = Call("coefficient", Call("physicalGate", a),
            Call("blankMemory", q, Call("physicalResidual", a, b)), Call("pair", i, k));
        var equation = Eq(output, Call("physicalResidual", a, Call("erase", b, i), k));
        return All("b", Multi, new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
            All("i", A, new Formula.Logic(new Formula.Relation(i, FormulaRelationOperator.MemberOf, b),
                FormulaLogicOperator.Implies, All("k", Memory, equation)))));
    }

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep.";
    private static Formula Attainment => Context(All("a", Multi,
        Exists("blank", A, Exists("U", Call("Unitary", Call("Prod", A, Memory)),
            Exists("x", Space, Exists("f", Space,
                And(Eq(Call("norm", x), D(1)), Eq(Call("norm", f), D(1)),
                    All("w", Call("Word", A, L), All("k", Memory,
                        Eq(Call("C", Id("U"), L, D(0), Call("J", Id("blank"), L, x), w, k),
                            Mul(Call("sector", L, a, w), Call("f", k))))))))))));
    private static Formula Id(string name) => F.Id(name);
    private static Formula A => Id("A");
    private static Formula a => Id("a");
    private static Formula x => Id("x");
    private static Formula f => Id("f");
    private static Formula w => Id("w");
    private static Formula k => Id("k");
    private static Formula Multi => Call("Multiset", A);
    private static Formula L => Call("L", a);
    private static Formula Memory => Call("Fin", Call("d", a));
    private static Formula Space => Call("Space", Memory);
    private static Formula Context(Formula body) => All("A", Id("Type"),
        new Formula.Logic(And(Call("Fintype", A), Call("DecidableEq", A), Call("Nonempty", A)),
            FormulaLogicOperator.Implies, body));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((right, left) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right));
}
