using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class WeightedPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/WeightedPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-state labelled path ledger is counted by a finite Laurent polynomial, with a scalar recurrence and exact charge-zero coefficient bridges.",
        H("Weighted Labelled Paths"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-transfer"),
                DeclarationHandle.Create(Prefix + "advance"), H("The explicit positive transfer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In state order A,D,E,H,I, the positive transfer rows are [z,z^2,1,0,z^(-1)], [1,z,z^(-1),1,0], [z^(-1),1,0,0,0], [0,z^(-1),0,0,0], and [1,0,0,0,0]. Each nonzero entry comes from its separately indexed labelled transition in PathData, including equal weights at distinct exits. The monomial records integer imbalance at +1, not a geometric path length."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar-path-recurrence"),
                DeclarationHandle.Create(Prefix + "pathPolynomial_recurrence"),
                H("The second-order Laurent recurrence"), StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "With terminal vector (1,z^(-1),0,0,0) and start row (1,z,0,0,0), pathPolynomial has initial values 2 and 4z and satisfies f_(m+2)=2z f_(m+1)+3z^(-1) f_m. The stronger vector recurrence follows by checking the explicit five-state transfer twice and inducting, not by fitting initial counts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-real-path-polynomial"),
                DeclarationHandle.Create(Prefix + "actualEvenPathPolynomial_eq_pathPolynomial"),
                H("Transfer counts actual even paths"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The sum of z to the accumulated charge over the finite positive-sector EvenPath type equals the transfer polynomial. The proof decomposes each labelled path into its start, indexed transitions, and terminal; equal transition weights still contribute as separate paths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-real-path-polynomial"),
                DeclarationHandle.Create(Prefix + "actualOddPathPolynomial_eq_shift"),
                H("Odd paths have the singleton shift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The odd terminal changes the positive-sector generating polynomial by one monomial shift. It is established by a separate induction over actual OddTail inhabitants and the singleton table, rather than by reusing the antipodal vector unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-charge-coefficients"),
                DeclarationHandle.Create(Prefix + "oddPath_zero_charge_card"),
                H("Odd zero-charge paths are one coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Extracting the zero-charge coefficient of the sum over actual odd paths yields the required shifted Laurent coefficient. The companion evenPath_zero_charge_card extracts coefficient zero directly. Sector reflection later doubles these positive-sector counts."))),
                DescribeRole.Theorem)), []));

    private static Formula RecurrenceFormula()
    {
        var m = F.Id("m");
        var left = Call("pathPolynomial", Add(m, D(2)));
        var first = Mul(Mul(D(2), Call("z", D(1))),
            Call("pathPolynomial", Add(m, D(1))));
        var second = Mul(Mul(D(3), Call("z", new Formula.Negate(D(1)))),
            Call("pathPolynomial", m));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("m"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
            new Formula.Relation(left, FormulaRelationOperator.Equal, Add(first, second))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
