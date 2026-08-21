using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class DifferentialTestingEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform reference directories have the exact diagonal-mutation escape probability.",
        H("Differential-Testing Escape Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("directory-escape-probability-exact"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Probability/DifferentialTestingEscape."
                        + "directory_escape_probability_exact"),
                H("Exact escape probability for diagonal mutants"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("A"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    Operatorname, Grp(F.Id("directoryEscapeProbability")),
                    Open, F.Id("f"), Close, Sp, Eq, Sp,
                    Open, D(1), Sp, Minus, Sp,
                    Frac,
                    Grp(Call("card", Call("Fix", F.Id("f")))),
                    Grp(Call("card", F.Id("Y")), Caret, Grp(Call("card", F.Id("A")))),
                    Close, Caret, Call("card", F.Id("A")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source directory g : A -> Y^A is Lean's curried finite function "
                            + "A -> A -> Y. Its diagonal mutant is f(g(a)(a)), and escape means "
                            + "that this diagonal output is absent from every directory row.")),
                    Paragraph(Text(
                        "The theorem uses the pinned uniform finite-PMF outer measure. The exact "
                            + "finite count is imported from D5.S0.Diagonal.EscapeCount.escaped_listing_card; "
                            + "the proof only bridges the source directory predicate and performs "
                            + "the cardinality-ratio arithmetic.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched for PMF.toOuterMeasure_uniformOfFintype_apply, "
                            + "Fintype cardinality bridges, and ENNReal subtraction/division. "
                            + "No repository declaration packages this source-specific directory "
                            + "notation with the uniform outer-measure statement."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Diagonal/EscapeCount"))]));

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
