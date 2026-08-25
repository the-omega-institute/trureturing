using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class RefinementShrinksIndistinguishabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementFactorization/"
            + "RefinementShrinksIndistinguishability."
            + "refinement_shrinks_indistinguishability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factor-map refinement transports fine-readout equality to the coarse readout.",
        H("Refinement Shrinks Indistinguishability"),
        Blocks(Describe.Lean(
            DescribeId.Create("refinement-shrinks-indistinguishability"),
            DeclarationHandle.Create(Declaration),
            H("Fine equality implies coarse equality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The concepts C and D are arbitrary readout channels on the same state "
                        + "type. Refinement is the source-defined factorization of the coarse "
                        + "readout through the fine one.")),
                Paragraph(Text(
                    "The factor map is applied to equality of the fine readouts. The two "
                        + "factorization equations then identify the resulting values with the "
                        + "coarse readouts.")),
                Paragraph(Text(
                    "No surjectivity, finiteness, or effectiveness premise is required; the "
                        + "statement retains the source theorem's full generality."))),
            DescribeRole.Theorem))));

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula coarse = F.Id("qC");
        Formula fine = F.Id("qD");
        Formula factor = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula refinement = Seq(
            Exists, Sp, factor, Colon, Sp, Arrow(fineType, coarseType), Comma, Sp,
            coarse, Sp, Eq, Sp, Apply(F.Id("compose"), factor, fine));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, coarseType, Comma, Sp, fineType,
            Colon, Sp, type, Comma,
            RowBreak, Grp(),
            coarse, Colon, Sp, Apply(F.Id("Concept"), stateType, coarseType), Comma, Sp,
            fine, Colon, Sp, Apply(F.Id("Concept"), stateType, fineType), Comma,
            RowBreak, Grp(),
            left, Comma, Sp, right, Colon, Sp, stateType, Comma,
            RowBreak, Grp(),
            Open, refinement, Close, Sp, Rightarrow, Sp,
            Open, Apply(fine, left), Sp, Eq, Sp, Apply(fine, right), Close, Sp,
            Rightarrow, Sp,
            Apply(coarse, left), Sp, Eq, Sp, Apply(coarse, right), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
