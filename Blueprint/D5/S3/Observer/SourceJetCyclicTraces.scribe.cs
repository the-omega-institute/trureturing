using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class SourceJetCyclicTracesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/SourceJetCyclicTraces.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A square-free source jet is the normalized sum of all ordered cyclic trace words.",
        H("Square-Free Source Jets as Cyclic Traces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-jet-is-closed-cyclic-traces"),
                DeclarationHandle.Create(Prefix + "source_jet_is_closed_cyclic_traces"),
                H("The full source coefficient is the permutation trace sum"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B_i be a finite family of square matrices and let k be positive. "
                            + "A source word survives the square-zero source rule exactly when "
                            + "every source label occurs at one unique position.")),
                    Paragraph(Text(
                        "Those surviving words are canonically equivalent to permutations of "
                            + "Fin k. Reindexing the finite sum gives the displayed coefficient "
                            + "with the nonzero 1/k normalization inherited from the kth term of "
                            + "the formal negative log-determinant expansion.")),
                    Paragraph(Text(
                        "The final clause applies the pinned matrix trace cyclicity theorem, so "
                            + "the ordered traces may also be grouped by cyclic word classes."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula permutation = Pi;
        Formula matrices = F.Id("B");
        Formula coefficient = Call("sourceJetCoefficient", matrices);
        Formula orderedProduct = Seq(
            Prod, Underscore, Grp(j, Eq, D(1)), Caret, Grp(k), Sp,
            matrices, Underscore, Grp(permutation, Open, j, Close));
        Formula traceSum = Seq(
            Frac, Grp(D(1)), Grp(k), Sp,
            Sum, Underscore, Grp(permutation, Sp, InMacro, Sp,
                F.Id("S"), Underscore, Grp(k)), Sp,
            Call("Tr", orderedProduct));
        Formula cyclicity = Seq(
            Call("Tr", Seq(F.Id("A"), F.Id("B"), F.Id("C"))), Sp, Eq, Sp,
            Call("Tr", Seq(F.Id("C"), F.Id("A"), F.Id("B"))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            k, Sp, Gt, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
            coefficient, Sp, Eq, Sp, traceSum, Sp, Land, RowBreak, Grp(),
            k, Sp, Neq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            F.Id("squareFreeWord"), Sp, Iff, Sp, F.Id("bijection"),
            Sp, Land, RowBreak, Grp(), cyclicity, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
