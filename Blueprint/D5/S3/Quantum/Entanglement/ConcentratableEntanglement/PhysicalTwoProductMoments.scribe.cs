using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.ConcentratableEntanglement;

internal sealed class PhysicalTwoProductMomentsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments.";
    private static readonly LibraryNoteRef Spectrum =
        LibraryNoteRef.Create("D5/L/HilbertOperators/wang2002nonorthogonal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All positive real moments of the actual reduced states of a coherent sum of two products have a two-value spectral formula.",
        H("Spectral moments for coherent two-product amplitudes"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-two-product-moments"),
                DeclarationHandle.Create(Owner + "physical_two_product_moments"),
                H("Exact real power traces and a normalization bound"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Spectrum),
                Blocks(
                    Paragraph(Text("A datum Ψ consists of a finite site set, a finite configuration type at each site, "
                        + "two local complex unit vectors per site, and complex coefficients a and b. "
                        + "The literal amplitude is a times the product of the first vectors plus b times the product of the second vectors. "
                        + "Its nonzero squared norm is N. The actual reduction ρ(U) sums the literal outer product over configurations on the complement "
                        + "and divides by N. The power in each trace is the real functional calculus on the reduced matrix.")),
                    Paragraph(Text("Write s(i) for the local squared overlap magnitude; the theorem proves s(i) ≤ 1. "
                        + "The normalization bound states N ≥ 2|a b|(1 − sqrt(product of s(i) over all sites)); this allows destructive phase interference. "
                        + "For each U, d(U) equals |a b|²/N² times one minus the overlap product on U times one minus the overlap product on its complement, "
                        + "and t(U) = sqrt(1 − 4d(U)). The finite Gram determinant and rank-two compression give the stated moment "
                        + "even when one spectral value vanishes. The two-value calculation is the grouped-cut form of Wang’s bipartite concurrence formula; "
                        + "here it is attached to the actual finite partial trace and extended to all positive real trace powers."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Binary(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(a, op, b);

    private static Formula Statement()
    {
        var k = F.Id("K");
        var x = F.Id("Q");
        var u = F.Id("U");
        var t = Call("t", x, u);
        var plus = new Formula.Fraction(Binary(Num(1), FormulaBinaryOperator.Add, t), Num(2));
        var minus = new Formula.Fraction(Binary(Num(1), FormulaBinaryOperator.Subtract, t), Num(2));
        var moment = Equal(Call("TrPower", x, k, u),
            Binary(new Formula.Power(P(plus), k), FormulaBinaryOperator.Add, new Formula.Power(P(minus), k)));
        var bound = All("i", Call("Sites", x),
            new Formula.Relation(Call("s", x, F.Id("i")), FormulaRelationOperator.LessThanOrEqual, Num(1)));
        var mass = new Formula.Relation(Call("PhaseBound", x), FormulaRelationOperator.LessThanOrEqual, Call("N", x));
        var guards = new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, k);
        return Disp(All("K", Seq(Mathbb, Grp(F.Id("R"))),
            All("Q", F.Id("NonzeroTwoProductData"),
                new Formula.Logic(P(guards), FormulaLogicOperator.Implies,
                    P(And(bound, And(mass, All("U", Call("Subsets", Call("Sites", x)), moment))))))));
    }
}
