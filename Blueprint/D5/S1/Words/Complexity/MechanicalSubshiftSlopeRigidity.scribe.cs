using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class MechanicalSubshiftSlopeRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every member of a lower mechanical word subshift has the slope's true-letter density, "
            + "so equality of two such subshifts forces equality of their slopes.",
        H("Density and Slope Rigidity of Mechanical Subshifts"),
        Blocks(
            Paragraph(Text(
                "Fix a real slope alpha in the half-open interval from zero to one and an arbitrary "
                + "real intercept rho. Every finite prefix of a subshift member is a factor of the "
                + "base lower mechanical word. Consequently its true count inherits the base "
                + "window discrepancy, and its asymptotic density recovers alpha without an "
                + "irrationality assumption.")),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-member-discrepancy"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity."
                        + "mechanical_wordSubshift_member_true_discrepancy"),
                H("Every subshift member has discrepancy below one"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    new Formula.Absolute(Subtract(
                        Call("wordPrefixTrueCount", F.Id("y"), F.Id("n")),
                        Multiply(F.Id("n"), F.Id("alpha")))),
                    FormulaRelationOperator.LessThan,
                    Num(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership realizes the length-n prefix as a factor beginning at some natural "
                    + "index. Equality of the factor letters identifies the two filtered true-count "
                    + "sets, so the public lower-mechanical window discrepancy applies directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-member-density"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity."
                        + "mechanical_wordSubshift_member_true_density"),
                H("Every subshift member has density equal to the slope"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), Sp, To, Sp, Infty), Sp,
                    new Formula.Fraction(
                        Call("wordPrefixTrueCount", F.Id("y"), F.Id("n")), F.Id("n")),
                    Sp, Eq, Sp, F.Id("alpha")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive prefix lengths, the discrepancy estimate traps the density "
                    + "between alpha minus one over n and alpha plus one over n. Both bounds tend "
                    + "to alpha, and the squeeze theorem gives the asserted limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-slope-rigidity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity."
                        + "mechanical_wordSubshift_slope_eq_of_eq"),
                H("Equal mechanical subshifts have equal slopes"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    Equal(
                        Call("wordSubshift",
                            Call("lowerMechanicalWord", F.Id("alpha"), F.Id("rho"))),
                        Call("wordSubshift",
                            Call("lowerMechanicalWord", F.Id("beta"), F.Id("sigma")))),
                    FormulaLogicOperator.Implies,
                    Equal(F.Id("alpha"), F.Id("beta"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The lower mechanical word at slope alpha belongs to its own subshift. Subshift "
                    + "equality makes that same word a member of the beta subshift, so its prefix "
                    + "density tends to both alpha and beta. Uniqueness of limits forces equality."))),
                DescribeRole.Theorem))));
}
