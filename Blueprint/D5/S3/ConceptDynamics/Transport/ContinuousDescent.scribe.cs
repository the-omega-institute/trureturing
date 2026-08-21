using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class ContinuousDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous fiber-constant map descends uniquely through a quotient map.",
        H("Continuous Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-descent"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/ContinuousDescent.continuous_descent"),
                H("Continuous maps descend uniquely through quotient maps"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a quotient map from X onto B, and let T be a continuous "
                            + "map from X to Y that is constant on every fiber of q.")),
                    Paragraph(Text(
                        "There is exactly one continuous map from B to Y whose composition "
                            + "with q is T. This is the continuous descent asserted by the "
                            + "formal-concept-dynamics source atom.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies IsQuotientMap.lift for existence, lift_comp "
                            + "for the commuting triangle, and ContinuousMap.cancel_right "
                            + "for uniqueness from surjectivity. The Lean theorem is a thin "
                            + "wrapper around those declarations."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula quotient = F.Id("B");
        Formula target = F.Id("Y");
        Formula quotientMap = F.Id("q");
        Formula targetMap = F.Id("T");
        Formula descended = Seq(Overline, Grp(targetMap));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, quotient, Comma, Sp, target,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", source), Comma, Sp,
            Typeclass("TopologicalSpace", quotient), Comma, Sp,
            Typeclass("TopologicalSpace", target), Comma, RowBreak, Grp(),
            quotientMap, Colon, Sp, Call("ContinuousMap", source, quotient), Comma, Sp,
            targetMap, Colon, Sp, Call("ContinuousMap", source, target), Comma,
            RowBreak, Grp(),
            Call("IsQuotientMap", quotientMap), Comma, Sp,
            Call("FactorsThrough", targetMap, quotientMap), Comma, RowBreak, Grp(),
            Exists, Bang, Sp, descended, Colon, Sp,
            Call("ContinuousMap", quotient, target), Comma, Sp,
            targetMap, Sp, Eq, Sp, descended, Sp, Circ, Sp, quotientMap, Dot));
    }
}
