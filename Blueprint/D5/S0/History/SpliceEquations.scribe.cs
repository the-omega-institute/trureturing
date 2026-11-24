using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class SpliceEquationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marker-history splicing follows the recursion on its second history.",
        H("Splice Equations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("splice-recursion-equations"),
                DeclarationHandle.Create(
                    "D5/S0/History/SpliceEquations.splice_recursion_equations"),
                H("Splicing is determined recursively on the second history"),
                StatementSource.FromAuthor(SpliceRecursionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every marker history h, splicing the empty history on the right "
                            + "returns h.")),
                    Paragraph(Text(
                        "For every marker epsilon and histories h and g, prefixing epsilon to "
                            + "the second argument prefixes the same marker to the splice. The "
                            + "two universally quantified equalities are asserted together."))),
                DescribeRole.Theorem),
            Paragraph(
                Text("A history is read from its last inserted marker to its first. Insertion at the end of the underlying list therefore prefixes the displayed word. Concatenating the two underlying lists in insertion order places the second displayed history before the first.")),
            Paragraph(
                Ref("D5/S0/History/SpliceEquations"),
                Text(" also carries a computational witness: splicing two one-marker histories yields the two-marker history whose leading marker comes from the second argument. The witness holds by reduction of the concatenation recursion.")))));

    private static Formula SpliceRecursionFormula()
    {
        Formula history = F.Id("h");
        Formula tail = F.Id("g");
        Formula marker = F.Id("epsilon");
        Formula historyType = F.Id("MarkerHistory");
        Formula markerType = F.Id("Marker");
        Formula singleton = Call("of", marker);
        Formula baseEquation = Seq(
            Forall, Sp, history, Colon, Sp, historyType, Comma, Sp,
            Call("splice", history, D(1)), Sp, Eq, Sp, history);
        Formula stepEquation = Seq(
            Forall, Sp, marker, Colon, Sp, markerType, Comma, Sp,
            history, Comma, Sp, tail, Colon, Sp, historyType, Comma, Sp,
            Call("splice", history, Seq(singleton, Sp, Times, Sp, tail)),
            Sp, Eq, Sp,
            singleton, Sp, Times, Sp, Call("splice", history, tail));

        return Disp(Seq(
            Parenthesized(baseEquation), Sp, Land, Sp,
            Parenthesized(stepEquation), Dot));
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
