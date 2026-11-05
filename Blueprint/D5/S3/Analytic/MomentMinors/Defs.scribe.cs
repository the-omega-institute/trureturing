using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/simic2018momentinequalities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moment gaps and their second minors.",
        H("Probability laws and parameter intervals"), Blocks(
            Entry("moment-minors-mean", "mean", "The first moment",
                "The mean of a real law is the integral of the identity function."),
            Entry("moment-minors-admissible", "Admissible", "The moment assumptions",
                "An admissible law is a Borel probability measure concentrated on strictly positive real values, with integrable first moment. Every real power indexed by I is integrable. The logarithmic moment and the first logarithmic moment are integrable when I contains zero and one, respectively."),
            Entry("moment-minors-lambda", "lam", "The normalized moment gap",
                "For s different from zero and one, lambda(s) is the difference between the power moment and the power of the mean, divided by s(s-1). At zero it is the logarithm of the mean minus the logarithmic moment. At one it is the first logarithmic moment minus the mean times its logarithm."),
            Entry("moment-minors-xi", "xi", "The second principal minor",
                "The value xi(s,t) is lambda(s)lambda(t) minus the square of lambda((s+t)/2)."),
            Entry("moment-minors-phi", "phi", "The iterated second minor",
                "The value phi(s,t,u,v) is xi(s,t)xi(u,v) minus the square of the alternating difference xi((s+u)/2,(t+v)/2)-xi((s+v)/2,(t+u)/2)."),
            Entry("moment-minors-sigma", "sigma", "Pairs with common displacement",
                "The value sigma(a,x) is xi(x,x+a)."),
            Entry("moment-minors-theta", "theta", "The displaced midpoint minor",
                "The value theta(a,x,y) is sigma(a,x)sigma(a,y) minus the square of sigma(a,(x+y)/2)."),
            Entry("moment-minors-claim-one", "claim1", "The eight-parameter inequality",
                "For every admissible law and every eight endpoint parameters in an interval, the product of the two phi values is at least the square of the alternating product of cross entries. Each cross entry is the alternating xi difference for the corresponding endpoint pairs. The exact source statement retains all eight independent parameters and their index order."),
            Entry("moment-minors-claim-two", "claim2", "The displaced-parameter inequality",
                "For every admissible law, interval and common displacement a, the product theta(a,x,y)theta(a,z,v) is at least the square of theta(a,(x+z)/2,(y+v)/2)-theta(a,(x+v)/2,(y+z)/2). The four endpoints and their translates by a belong to the interval, which also contains every required midpoint."),
            Entry("moment-minors-combined-claim", "claim", "Both inequalities",
                "The combined claim is the conjunction of the eight-parameter inequality and the displaced-parameter inequality."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/MomentMinors/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
