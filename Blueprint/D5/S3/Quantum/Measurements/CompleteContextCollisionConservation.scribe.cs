using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class CompleteContextCollisionConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete complementary rank-one measurements conserve collisions at operator and scalar level.",
        H("Complete Context Collision Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-context-collision-conservation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/CompleteContextCollisionConservation."
                        + "complete_context_collision_conservation"),
                H("Complete context collision conservation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take n+2 complete rank-one record measurements in dimension n+1. "
                            + "Their public trace-overlap equation states orthogonality within "
                            + "each context and inverse-dimension overlap between contexts.")),
                    Paragraph(Text(
                        "The frozen complete-context tomography theorem separates matrices by "
                            + "their projector traces. Applying that separator to the induced "
                            + "frame map and then evaluating on matrix units gives the operator "
                            + "identity with the canonical coordinate-swap permutation matrix.")),
                    Paragraph(Text(
                        "The scalar collision clause is the frozen complete-context purity "
                            + "identity applied to the same context family and density matrix. "
                            + "Prime-dimensional Weyl context families are instances of these "
                            + "public complete-context hypotheses."))),
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
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula inverseDimension = new Formula.Fraction(D(1), dimension);
        Formula context = Seq(family, Underscore, Grp(contextIndex));
        Formula otherContext = Seq(family, Underscore, Grp(otherContextIndex));
        Formula projector = Call("projector", context, outcome);
        Formula otherProjector = Call("projector", otherContext, otherOutcome);
        Formula overlapValue = Call(
            "if",
            Seq(contextIndex, Sp, Eq, Sp, otherContextIndex),
            Call("if", Seq(outcome, Sp, Eq, Sp, otherOutcome), D(1), D(0)),
            inverseDimension);
        Formula matrixType = Call("Matrix", outcomeType, outcomeType, complex);
        Formula productIndexType = Seq(Open, outcomeType, Sp, Times, Sp, outcomeType, Close);
        Formula productMatrixType = Call(
            "Matrix", productIndexType, productIndexType, complex);
        Formula operatorSum = Seq(
            Sum, Underscore, Grp(contextIndex), Sp,
            Sum, Underscore, Grp(outcome), Sp,
            Call("Kronecker", projector, projector));
        Formula swap = Call("PermMatrix", Call("prodComm", outcomeType, outcomeType));
        Formula probability = Call("basisProbability", rho, context, outcome);
        Formula probabilitySquare = new Formula.Power(probability, D(2));
        Formula purity = Call("ReTr", Seq(rho, Caret, Grp(D(2))));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            family, Colon, Sp, contextIndexType, Sp, To, Sp,
            Call("RankOneContext", dimension), Comma, Esc,
            rho, Colon, Sp, matrixType, Comma, RowBreak, Grp(),
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
            Open, operatorSum, Sp, Eq, Sp,
            F.Id("I"), Underscore, Grp(productMatrixType), Sp, Plus, Sp, swap,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Sum, Underscore, Grp(contextIndex), Sp,
            Sum, Underscore, Grp(outcome), Sp, probabilitySquare, Sp,
            Eq, Sp, D(1), Sp, Plus, Sp, purity,
            Close, Dot));
    }
}
