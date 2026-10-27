using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class MatharSameParityRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source permutation count in OEIS A152661 satisfies Mathar's first recurrence at every natural index at least four.",
        H("Equal parity in the first two values"),
        Blocks(
            Paragraph(Text("OEIS A152661 defines a(n) as the number of permutations of {1,...,n} "
                + "whose first two entries have the same parity, for n at least two. "
                + "Its first conjectural FORMULA, attributed to R. J. Mathar, is the recurrence below. "
                + "The source is https://oeis.org/search?q=id%3AA152661&fmt=text. "
                + "The entry's even and odd factorial-binomial formulas are prior formulas. "
                + "Parity here always means parity of a natural value, rather than parity in a finite ring.")),
            Describe.Lean(DescribeId.Create("mathar-same-parity-count"),
                DeclarationHandle.Create(Prefix + "a"), H("The permutation count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A permutation p of Fin n represents the natural word with value "
                    + "p(i).val+1 in position i+1. For n at least two, a(n) is the integer cast "
                    + "of the cardinality of the permutations satisfying "
                    + "(p(0).val+1) mod 2 = (p(1).val+1) mod 2. "
                    + "For the two indices below this domain, a(n) is defined to be zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mathar-same-parity-recurrence"),
                DeclarationHandle.Create(Prefix + "result"), H("The integer recurrence"),
                StatementSource.FromAuthor(Recurrence()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are e natural values of one parity and o of the other. "
                        + "An ordered distinct first pair therefore has e(e-1)+o(o-1) choices. "
                        + "Reading this pair decomposes the actual permutation subtype into disjoint "
                        + "completion fibers. Each fiber has (n-2)! elements by the finite "
                        + "partial-injection extension count. Consequently a(n) is "
                        + "[e(e-1)+o(o-1)](n-2)!; this is an equality with the source cardinality.")),
                    Paragraph(Text("At n=2k+2 the pair count is 2k(k+1), and at n=2k+3 "
                        + "it is 2(k+1)^2. In particular a(2)=0 and a(4)=8. "
                        + "Substituting these two count formulas and the factorial successor identity "
                        + "proves the recurrence in both parity cases, including n=4. "
                        + "All coefficients and sequence values in the displayed equality are integers; "
                        + "the indices n-1 and n-2 are natural indices."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Recurrence()
    {
        Formula n = F.Id("n");
        Formula first = Times(Parens(Subtract(D(3), n)), Call("a", n));
        Formula second = Times(Times(D(2), Parens(Subtract(n, D(2)))),
            Call("a", Subtract(n, D(1))));
        Formula third = Times(Times(Times(Parens(Subtract(n, D(1))),
            Parens(Subtract(n, D(2)))), Parens(Subtract(n, D(3)))),
            Call("a", Subtract(n, D(2))));
        Formula equality = new Formula.Relation(Add(Add(first, second), third),
            FormulaRelationOperator.Equal, D(0));
        Formula condition = new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, n);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(condition, FormulaLogicOperator.Implies, Parens(equality))));
    }
}
