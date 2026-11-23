using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class LocalStatisticCutoffsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/LocalStatisticCutoffs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local neighborhood counts control the change in a tuple statistic under a new cutoff.",
        H("Changing the Index Set of a Local Tuple Statistic"),
        Blocks(
            Paragraph(Text(
                "Let S and T be nonempty subsets of a finite index set J with real frequencies g. "
                + "Write s and t for their respective sizes and b for the size of their symmetric "
                + "difference. Fix a natural number k and a real score on ordered distinct-index "
                + "tuples of length k+1. The score has magnitude at most M≥0. For a nonzero score, "
                + "all frequencies of the tuple have distance at most R from its first frequency. "
                + "For each index in S∪T the number of indices of S∪T within distance 2R of its "
                + "frequency is at most the natural number D. Let A(U) sum the scores over ordered "
                + "tuples with every index in U. Write L for M times the falling factorial of "
                + "max(D−1,0) of order k.")),
            Describe.Lean(
                DescribeId.Create("local-statistic-cutoff"),
                DeclarationHandle.Create(Owner + ".local_statistic_cutoff"),
                H("Local tuple sums vary with the changed indices"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Only tuples with a changed index can contribute to the difference of the "
                        + "two sums. Mark one slot containing a changed index. Every other slot is "
                        + "within distance 2R of the marked frequency by the triangle inequality, "
                        + "including when the mark is outside the first slot. Fix the marked "
                        + "index and slot and assign distinct entries from its neighborhood after "
                        + "erasing the marked index itself.")),
                    Paragraph(Text(
                        "When bounding one sum, use only the first slot as the mark. Its size is "
                        + "then bounded by the number of eligible first indices times L. "
                        + "Compare the sums over the larger denominator and use this bound for the "
                        + "renormalization of the smaller set. The magnitude of each normalized "
                        + "sum is at most L, giving the second bound."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        var s = F.Id("s");
        var t = F.Id("t");
        var k = F.Id("k");
        var b = F.Id("b");
        var l = F.Id("L");
        var left = new Formula.Absolute(Seq(
            new Formula.Fraction(Call("A", F.Id("S")), s), Minus,
            new Formula.Fraction(Call("A", F.Id("T")), t)));
        var changed = Add(Multiply(Grp(Add(k, D(1))), b), new Formula.Absolute(Seq(s, Minus, t)));
        var numerator = Multiply(l, Grp(changed));
        var variableBound = new Formula.Fraction(numerator, Call("max", s, t));
        return Disp(new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual,
            Call("min", variableBound, Multiply(D(2), l))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
