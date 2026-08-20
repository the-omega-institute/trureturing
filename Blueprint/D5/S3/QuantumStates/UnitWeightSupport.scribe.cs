using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class UnitWeightSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive trace-one matrix with unit weight on a self-adjoint projection is supported on that projection.",
        H("Unit Weight Forces Projection Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-projection-weight-forces-support"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/UnitWeightSupport."
                        + "unit_weight_support_face"),
                H("Unit projection weight confines the state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
                    CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("n"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, Rho, Comma, Sp, F.Id("P"), Sp, InMacro, Sp,
                    Call("Matrix", F.Id("n"), F.Id("n"), Mathbb, Grp(F.Id("C"))), Comma, Esc,
                    Call("PosSemidef", Rho), Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(Star), Sp, Eq, Sp, F.Id("P"), Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(D(2)), Sp, Eq, Sp, F.Id("P"), Sp, Land, Sp,
                    Call("trace", Rho), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Call("trace", Seq(Rho, Thin, F.Id("P"))), Sp, Eq, Sp, D(1),
                    Sp, Rightarrow, Sp,
                    Rho, Sp, Eq, Sp, F.Id("P"), Thin, Rho, Thin, F.Id("P"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hypotheses are the source state primitives: positivity and trace-one normalization for rho, together with self-adjointness and idempotence for the projection P.")),
                    Paragraph(Text(
                        "Unit trace weight on P gives zero trace weight on the complementary projection I minus P. The exact zero-weight support-face theorem then yields rho equals P rho P.")),
                    Paragraph(Text(
                        "No support condition is assumed in advance; the compression is the public conclusion forced by the source weight test."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
