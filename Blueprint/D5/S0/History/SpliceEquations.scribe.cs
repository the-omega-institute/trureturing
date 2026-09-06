using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class SpliceEquationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marker-history splicing is pinned by its defining recursion, not by a library alias.",
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
                Text("The marker-history carrier defines splicing through the free-monoid product. That definition is compact, but on its own it leaves a reader unable to check that the operation is the intended one: any product-shaped alias would typecheck equally well.")),
            Paragraph(
                Text("The theorem `splice_recursion_equations` states the two equations that determine splicing on its second argument. The empty history is the right unit, and prefixing a marker to the second argument prefixes the same marker to the result. Together they characterize the operation recursively, so the carrier's definition is verified against the intended recursion rather than assumed to implement it.")),
            Paragraph(
                Ref("D5/S0/History/SpliceEquations"),
                Text(" also carries a computational witness: splicing two one-marker histories yields the two-marker history whose leading marker comes from the second argument. The witness holds by reduction, so it exercises the definition itself rather than a restatement of it.")))));

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
