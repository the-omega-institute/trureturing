using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class FixedPointFreeEscapeProbabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = new Formula.Logic(
            Equal(Call("card", Call("Fix", F.Id("f"))), Num(0)),
            FormulaLogicOperator.Implies,
            Equal(Call("escapeProbability", F.Id("f")), Num(1)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A fixed-point-free twist gives uniform escape probability one.",
            H("Fixed-Point-Free Escape Probability"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fixed-point-free-escape-probability-is-one"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/FixedPointFreeEscapeProbability.fixed_point_free_escape_probability_eq_one"),
                    H("Fixed-point-free escape has probability one"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("Y"), Esc,
                        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("A"), Close,
                        CloseBracket, Sp,
                        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                        CloseBracket, Sp,
                        OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("A"), Close,
                        CloseBracket, Sp,
                        OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("Y"), Close,
                        CloseBracket, Comma, Esc,
                        Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("Y"), Comma, Esc,
                        statement))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For finite nonempty types A and Y, escapeProbability is the real "
                            + "cardinality ratio of twisted-diagonal escaped listings to all listings. "
                            + "If the twist has no fixed point, this ratio is exactly one.")),
                        Paragraph(Text(
                            "The proof is a thin wrapper over the exact fixed-point-free escaped-listing "
                            + "cardinality theorem in D5.S0.Diagonal.CaptureCount, together with the "
                            + "finite function-cardinality identity and elementary real division.")),
                        Paragraph(Text(
                            "This is a partial closure of clause (i) of the source corollary. Its "
                            + "monotonicity, asymptotic, Poisson, and dense-phase clauses remain open."))),
                    DescribeRole.Theorem)),
            []));
    }
}
