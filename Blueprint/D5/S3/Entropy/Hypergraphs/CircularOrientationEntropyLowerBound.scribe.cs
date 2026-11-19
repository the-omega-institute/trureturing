using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Hypergraphs;

internal sealed class CircularOrientationEntropyLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-uniformity entropy lower bound for circular orientations.",
        H("Circular orientation entropy: an explicit lower bound"),
        Blocks(
            Paragraph(Text("For n > r, circular n r has vertices Fin n and the n labelled edges " +
                "{i,i+1,...,i+r-1}, with vertex indices reduced modulo n. Independently choose " +
                "one vertex uniformly from each edge, and let X be the cardinality of the image " +
                "of the resulting choice function. The entropy is exactly the existing " +
                "OrientationEntropyBalance.entropyX: the finite sum of -p log₂ p over " +
                "k=0,...,n, with p the literal orientation count for X=k divided by r^n. " +
                "The convention at zero is 0 log₂ 0=0. This is not the circular-maximality claim.")),
            Definition("a", "Endpoint avoidance probability", Pow(
                Par(Subtract(Num(1), Frac(Num(1), Id("r")))), Subtract(Id("r"), Num(1))),
                "The exponent r-1 is natural subtraction. The base and division are real. " +
                "For r≥3 this is the probability that r-1 independent incident edges avoid a fixed endpoint."),
            Definition("q", "Good-endpoint probability", Multiply(Call("a", Id("r")),
                Par(Subtract(Num(1), Call("a", Id("r"))))),
                "The left incident choices avoid one endpoint, while the disjoint right incident choices hit the other endpoint at least once."),
            Definition("b", "Bernoulli variance threshold", Frac(
                Subtract(Id("r"), Num(1)), Pow(Id("r"), Num(2))),
                "The numerator r-1 is subtraction after casting r to the reals. " +
                "For an integer k between 1 and r-1, p=k/r satisfies p(1-p)≥b(r)."),
            Definition("c", "Characteristic-function decay constant", Multiply(Call("q", Id("r")),
                Par(Subtract(Num(1), QCall("Real", "exp", Multiply(new Formula.Negate(Num(2)), Call("b", Id("r"))))))),
                "The proof establishes c(r)>0 for every natural r≥3."),
            Definition("K", "Explicit entropy offset", Call("max", Frac(Num(1), Num(2)),
                Multiply(Frac(Num(1), Num(2)), QCall("Real", "logb", Num(2),
                    Frac(Q("Real", "pi"), Call("c", Id("r")))))),
                "K depends only on r. The maximum with one half includes every integer in the finite regime r<n<2r, not just sufficiently large n."),
            Describe.Lean(DescribeId.Create("circular-orientation-entropy-whole-one-two"),
                DeclarationHandle.Create(Prefix + "whole_theorem_one_two"),
                H("The full fixed-uniformity lower bound"),
                StatementSource.FromAuthor(F.Disp(MainFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("All natural r≥3 and n>r are quantified. The functions circular and entropyX " +
                        "in the formula are the existing CircularOrientationEntropy.circular and " +
                        "OrientationEntropyBalance.entropyX, not new distributions or abstract hypotheses. " +
                        "All fractions and logarithms in the inequality are real-valued; logb 2 is the base-two logarithm.")),
                    Paragraph(Text("For n≥2r, choose m=⌊n/(2r)⌋ edges starting at 2rj. " +
                        "The proof verifies their actual cyclic geometry, including the neighbourhood crossing zero. " +
                        "Splitting the finite choice space into selected and revealed coordinates gives, on every " +
                        "actual fibre, X=B+Σ Zj. Disjoint coordinate supports give the joint generating function " +
                        "of the good-endpoint events, each with probability q(r). Their occurrence forces " +
                        "the corresponding unseen-vertex count between 1 and r-1. These are proved properties " +
                        "of the original orientation law, not assumptions of the theorem.")),
                    Paragraph(Text("Averaging the fibre characteristic functions after taking absolute values " +
                        "removes the random phase B. The resulting decay is exp(-m c(r) sin²(t/2)). " +
                        "Finite Fourier inversion, the sine lower bound and the Gaussian integral bound every " +
                        "point mass by √(πr/(c(r)n)). The largest-atom entropy inequality yields the displayed " +
                        "bound. Nonnegativity of the same finite entropy handles r<n<2r. The constant is not " +
                        "asserted uniform in r, and no entropy-maximality conclusion is made."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula rhs, string explanation) =>
        Describe.Lean(DescribeId.Create("circular-orientation-entropy-constant-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(All("r", Naturals(), Equal(Call(name, Id("r")), rhs)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula MainFormula() => All("r", Naturals(), All("n", Naturals(),
        Implies(Le(Num(3), Id("r")), Implies(Lt(Id("r"), Id("n")),
            Le(Subtract(Multiply(Frac(Num(1), Num(2)), QCall("Real", "logb", Num(2),
                Frac(Id("n"), Id("r")))), Call("K", Id("r"))),
                QCall("OrientationEntropyBalance", "entropyX", Id("r"),
                    QCall("CircularOrientationEntropy", "circular", Id("n"), Id("r"))))))));

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Par(Formula a) => F.Seq(F.Open, a, F.Close);
    private static Formula Q(string owner, string name) => F.Seq(Id(owner), F.Dot, Id(name));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Q(owner, name), [.. args]);
}
