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
                DescribeId.Create("interval-affine-faces-and-endpoint-counterexample"),
                DeclarationHandle.Create(Prefix + "interval_affine_faces_and_endpoint_counterexample"),
                H("Connected affine faces do not prevent a nonglobal local minimum"),
                StatementSource.FromAuthor(CounterexampleFormula()),
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

    private static Formula CounterexampleFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula interval = F.Id("K");
        Formula endpoints = F.Id("P");
        Formula face = F.Id("Face");
        Formula m = F.Id("m");
        Formula b = F.Id("b");
        Formula affine = Call("Affine", m, b);
        Formula local = Call("LocalMin", F.Id("id"), endpoints, D(1));
        Formula global = Call("GlobalMin", F.Id("id"), endpoints, D(1));
        return Disp(Seq(
            Call("IsCompact", interval), Sp, Land, Sp,
            Call("IsCompact", endpoints), Sp, Land, Sp,
            Open, Forall, Sp, m, Comma, Sp, b, Colon, Sp, real, Comma, Esc,
            Call("IsConnected", Call(face, affine)), Close, Sp, Land, Sp,
            local, Sp, Land, Sp, Neg, global, Dot));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
