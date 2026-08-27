using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class CompleteContextPurityIdentitiesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete complementary rank-one measurements express purity exactly in Born-probability coordinates.",
        H("Complete Context Purity Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-context-purity-identities"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/CompleteContextPurityIdentities."
                        + "complete_context_purity_identities"),
                H("Complete context purity identities"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take n+2 complete rank-one record measurements in dimension n+1. The "
                            + "public overlap equation gives Kronecker trace overlap within one "
                            + "context and constant inverse-dimension overlap between distinct "
                            + "contexts.")),
                    Paragraph(Text(
                        "The overlap equation derives both pairwise orthogonality of the trace-zero "
                            + "measurement projections and reconstruction of every trace-zero "
                            + "Hermitian state. The existing probability Pythagoras theorem then "
                            + "has zero residual.")),
                    Paragraph(Text(
                        "Each context's Born coordinates sum to one. Expanding the centered "
                            + "squares across all n+2 contexts therefore gives the equivalent "
                            + "uncentered identity: the total squared probability is one plus the "
                            + "real trace purity."))),
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

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula dimension = Seq(n, Sp, Plus, Sp, D(1));
        Formula contextCount = Seq(n, Sp, Plus, Sp, D(2));
        Formula family = F.Id("C");
        Formula contextIndex = F.Id("l");
        Formula otherContextIndex = F.Id("k");
        Formula outcome = F.Id("j");
        Formula otherOutcome = F.Id("r");
        Formula rho = Rho;
        Formula contextIndexType = Call("Fin", contextCount);
        Formula outcomeType = Call("Fin", dimension);
        Formula inverseDimension = new Formula.Fraction(D(1), dimension);
        Formula context = Seq(family, Underscore, Grp(contextIndex));
        Formula probability = Call("basisProbability", rho, context, outcome);
        Formula projector = Call("projector", context, outcome);
        Formula otherProjector = Call(
            "projector",
            Seq(family, Underscore, Grp(otherContextIndex)),
            otherOutcome);
        Formula overlapValue = Call(
            "if",
            Seq(contextIndex, Sp, Eq, Sp, otherContextIndex),
            Call("if", Seq(outcome, Sp, Eq, Sp, otherOutcome), D(1), D(0)),
            inverseDimension);
        Formula centeredSquare = Seq(
            Grp(probability, Sp, Minus, Sp, inverseDimension), Caret, Grp(D(2)));
        Formula probabilitySquare = Seq(probability, Caret, Grp(D(2)));
        Formula purity = Call("ReTr", Seq(rho, Caret, Grp(D(2))));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            family, Colon, Sp,
            contextIndexType, Sp, To, Sp,
            Call("RankOneContext", dimension), Comma, Esc,
            rho, Colon, Sp,
            Call("Matrix", outcomeType, outcomeType, Seq(Mathbb, Grp(F.Id("C")))), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, contextIndex, Colon, Sp, contextIndexType, Comma, Sp,
            Call("IsRecordMeasurement", Call("projector", context)), Close, Sp,
            Land, RowBreak, Grp(),
            Open, Forall, Sp,
            contextIndex, Comma, Sp, otherContextIndex, Colon, Sp, contextIndexType, Comma, Sp,
            outcome, Comma, Sp, otherOutcome, Colon, Sp, outcomeType, Comma, RowBreak, Grp(),
            Call("Tr", Seq(projector, Sp, Cdot, Sp, otherProjector)), Sp,
            Eq, Sp, overlapValue, Close, Sp, Land, RowBreak, Grp(),
            Call("PosSemidefinite", rho), Sp, Land, Sp,
            Call("Tr", rho), Sp, Eq, Sp, D(1), Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Sum, Underscore, Grp(contextIndex), Sp,
            Sum, Underscore, Grp(outcome), Sp, centeredSquare, Sp,
            Eq, Sp, purity, Sp, Minus, Sp, inverseDimension,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Sum, Underscore, Grp(contextIndex), Sp,
            Sum, Underscore, Grp(outcome), Sp, probabilitySquare, Sp,
            Eq, Sp, D(1), Sp, Plus, Sp, purity,
            Close, Dot));
    }
}
