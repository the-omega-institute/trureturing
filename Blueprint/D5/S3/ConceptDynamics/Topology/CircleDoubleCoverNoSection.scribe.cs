using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class CircleDoubleCoverNoSectionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection."
            + "no_continuous_global_section";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squaring double cover of the unit circle has no continuous global section.",
        H("No Continuous Global Section of the Circle Double Cover"),
        Blocks(Describe.Lean(
            DescribeId.Create("circle-double-cover-no-continuous-section"),
            DeclarationHandle.Create(Declaration),
            H("The circle squaring map has no continuous right inverse"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source map is the canonical squaring map on the exact unit-circle "
                        + "carrier: a section s would satisfy s(z)^2 = z at every point.")),
                Paragraph(Text(
                    "To rule out such a section, compose it with the angle exponential and "
                        + "divide by the half-angle exponential. The resulting continuous map "
                        + "takes values in the finite set {1,-1}, so connectedness of the real "
                        + "line forces it to be constant.")),
                Paragraph(Text(
                    "The values at 0 and 2*pi differ by a sign because Circle.exp(2*pi) = 1 "
                        + "while Circle.exp(pi) = -1. This contradicts the constant-sign "
                        + "conclusion, proving that no continuous global section exists."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula circle = F.Id("Circle");
        Formula section = F.Id("s");
        Formula point = F.Id("z");
        Formula sectionType = new Formula.TypeArrow(circle, circle);
        Formula sectionApplication =
            new Formula.FunctionCall(FormulaIdentifier.Create("s"), [point]);
        Formula sectionEquation = Seq(
            Forall, Sp, point, Colon, Sp, circle, Comma, Sp,
            new Formula.Power(sectionApplication, new Formula.Number(2)), Sp, Eq, Sp, point);
        Formula sectionProperty = Seq(
            Call("Continuous", section), Sp, Land, Sp, sectionEquation);

        return Disp(Seq(
            Neg, Sp, Exists, Sp, section, Colon, Sp, sectionType, Comma, Sp,
            sectionProperty, Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
