using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class IntervalLocalMinimumCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one-dimensional interval has connected affine exposed faces but a nonglobal relative local minimum.",
        H("A One-Dimensional Local-Minimum Counterexample"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval-model"),
                DeclarationHandle.Create(Prefix + "intervalK"),
                H("The closed unit interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "intervalK is the closed real interval [0,1], which supplies the compact "
                        + "convex model in the one-dimensional obstruction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pure-endpoints"),
                DeclarationHandle.Create(Prefix + "pureEndpoints"),
                H("The two pure endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "pureEndpoints is the two-point set {0,1}, representing the extreme "
                        + "points of the interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exposed-face"),
                DeclarationHandle.Create(Prefix + "exposedFace"),
                H("Affine exposed faces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real function g, exposedFace g consists of the points in the "
                        + "interval at which g attains its maximum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("relative-local-minimum"),
                DeclarationHandle.Create(Prefix + "relativeLocalMinimum"),
                H("Relative local minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "relativeLocalMinimum records a positive-radius neighborhood inside a "
                        + "set on which the function value is no smaller than at the chosen point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("global-minimum"),
                DeclarationHandle.Create(Prefix + "globalMinimum"),
                H("Global minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "globalMinimum requires the chosen point to have value no larger than "
                        + "the function value at every point of the set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The local-to-global implication"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The claim asserts that compactness of the interval and endpoint set, "
                            + "together with connected maximum faces for every affine function, "
                            + "would make every relative local minimum on the endpoint set a "
                            + "global minimum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Connected affine faces do not prevent a nonglobal local minimum"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every affine function m x + b, its maximum face on [0,1] is "
                            + "connected: it is the whole interval when m=0 and a singleton "
                            + "endpoint when m is nonzero. The endpoint set itself is compact.")),
                    Paragraph(Text(
                        "With the coordinate function x restricted to {0,1}, the point 1 is a "
                            + "relative local minimum: a radius-one-half neighborhood in the "
                            + "endpoint set contains no point other than 1. It is not a global "
                            + "minimum because the endpoint 0 has the smaller coordinate.")),
                    Paragraph(Text(
                        "This is the explicit one-dimensional obstruction from the source: "
                            + "connected pure edges and compactness alone do not turn every "
                            + "relative local minimum into a global minimum."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula interval = F.Id("intervalK");
        Formula endpoints = F.Id("pureEndpoints");
        Formula face = F.Id("exposedFace");
        Formula m = F.Id("m");
        Formula b = F.Id("b");
        Formula affine = Call("Affine", m, b);
        Formula faces = All("m", real, All("b", real,
            Call("IsConnected", Call(face, affine))));
        Formula assumptions = And(Call("IsCompact", interval),
            And(Call("IsCompact", endpoints), faces));
        Formula function = F.Id("f");
        Formula point = F.Id("p");
        Formula conclusion = All("f", Arrow(real, real), All("p", real,
            Arrow(Call("relativeLocalMinimum", function, endpoints, point),
                Call("globalMinimum", function, endpoints, point))));
        return Equivalence(Local("claim"), Arrow(assumptions, conclusion));
    }

    private static Formula Local(string name) =>
        Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot,
            F.Id("QuantumContext"), Dot, F.Id("IntervalLocalMinimumCounterexample"),
            Dot, F.Id(name))));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) =>
        Seq(Left, Open, value, Right, Close);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula Call(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
}
