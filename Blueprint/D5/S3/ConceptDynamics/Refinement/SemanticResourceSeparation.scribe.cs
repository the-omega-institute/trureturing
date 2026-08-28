using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class SemanticResourceSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "More semantic targets than allowed algorithms force a resource-unreachable target.",
        H("Semantic Sufficiency Beyond Finite Resources"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semantic-sufficiency-can-exceed-finite-resources"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/SemanticResourceSeparation."
                        + "semantic_sufficiency_can_exceed_finite_resources"),
                H("Semantic sufficiency can exceed finite resources"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target carrier and the image of the concept readout are finite, "
                            + "and the target carrier is nonempty. The finite allowed class is "
                            + "exactly the class of factor maps whose declared cost is within budget.")),
                    Paragraph(Text(
                        "Restricting every allowed factor to the readout image yields no more "
                            + "functions than there are allowed algorithms. The strict cardinality "
                            + "hypothesis therefore supplies a target function missing from those restrictions.")),
                    Paragraph(Text(
                        "Composing that function with the readout constructs the target. Nonemptiness "
                            + "extends the function off the image, proving semantic refinement, while "
                            + "membership in the budget class would contradict how it was selected."))),
                DescribeRole.Theorem))));

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula SeparationFormula()
    {
        Formula x = F.Id("X");
        Formula b = Subscript(F.Id("B"), F.Id("C"));
        Formula y = F.Id("Y");
        Formula readout = F.Id("C");
        Formula allowed = Subscript(F.Id("A"), F.Id("r"));
        Formula target = F.Id("T");
        Formula cost = F.Id("cost");
        Formula budget = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula functionType = Seq(b, Sp, To, Sp, y);
        Formula range = Call("range", readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, b, Comma, Sp, y, Colon, Sp, type,
            Comma, Sp, Typeclass("Fintype", y), Comma, Sp,
            Typeclass("Nonempty", y),
            Comma, RowBreak, Grp(),
            readout, Colon, Sp, x, Sp, To, Sp, b, Comma, Sp,
            Typeclass("Fintype", range), Comma, Sp,
            cost, Colon, Sp, F.Id("ResourceCost"), Comma, Sp,
            budget, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            allowed, Colon, Sp, Call("Finset", functionType), Comma, RowBreak, Grp(),
            allowed, Sp, Eq, Sp,
            Seq(OpenBrace, F.Id("f"), Colon, Sp, functionType, Sp, Mid, Sp,
                Call("cost", F.Id("f")), Sp, Le, Sp, budget, CloseBrace),
            Comma, RowBreak, Grp(),
            Cardinality(y), Caret, Grp(Cardinality(range)), Sp, Gt, Sp,
            Cardinality(allowed), Sp, Rightarrow, Sp,
            Exists, Sp, target, Colon, Sp, x, Sp, To, Sp, y, Comma, RowBreak, Grp(),
            Call("Refines", target, readout), Sp, Land, Sp, Neg, Sp,
            Call("ResourceRefines", cost, budget, target, readout), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
