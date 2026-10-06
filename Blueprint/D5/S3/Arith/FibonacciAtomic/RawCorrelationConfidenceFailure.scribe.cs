using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RawCorrelationConfidenceFailureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse and forward first-gate events have exact masses under the heterogeneous product law.",
        H("First-Gate Event Masses"),
        Blocks(
            Paragraph(Text(
                "For rho in (0,1/8], let the first high coordinate have parameter 1-3rho "
                + "and the second and third coordinates have parameter 2rho. "
                + "The product mass of a Boolean triple is the product of its three Bernoulli masses. "
                + "The reverse event is (false,true,true), while the forward event is (true,false,true).")),
            Describe.Lean(
                DescribeId.Create("raw-correlation-confidence-failure"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exact reverse and forward event masses"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem evaluates both event masses by the finite product sum. "
                    + "The reverse mass is 12 rho cubed. The forward mass is "
                    + "2 rho (1-3rho) (1-2rho)."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Sq(Formula a) => Seq(Par(a), Caret, Grp(D(2)));
    private static Formula Par(Formula value) => Seq(Open, value, Close);

    private static Formula ResultFormula()
    {
        var rho = V("rho");
        var reverse = Call("Mminus", rho);
        var forward = Call("Mplus", rho);
        var range = Seq(D(0), Lt, rho, Leq, Fraction(D(1), D(8)));
        var body = Seq(
            reverse, Sp, Eq, Sp,
            Seq(D(12), Sq(rho)), Sp, Land, Sp,
            forward, Sp, Eq, Sp,
            Seq(D(2), rho, Par(Seq(D(1), Minus, D(3), rho)),
                Par(Seq(D(1), Minus, D(2), rho))));
        return Seq(Forall, Sp, rho, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(V("R"))), Sp, Par(range), Comma, Sp, body);
    }
}
