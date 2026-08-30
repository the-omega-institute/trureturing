using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CompletionConstants;

internal sealed class LiCaratheodoryIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula z = F.Id("z");
        Formula lambda = F.Id("lambdaOne");
        Formula mobius = Call("mobiusCoordinate", z);
        Formula disk = new Formula.Relation(Call("norm", z), FormulaRelationOperator.LessThan, D(1));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan,
            Call("re", lambda));
        Formula identity = Equal(
            Call("liCaratheodory", z),
            Multiply(new Formula.Fraction(D(1), lambda),
                Call("logDeriv", F.Id("xiReading"), mobius)));
        Formula halfPlane = new Formula.Relation(
            new Formula.Fraction(D(1), D(2)), FormulaRelationOperator.LessThan,
            Call("re", mobius));
        Formula normalization = Equal(Call("liCaratheodory", D(0)), D(1));
        Formula leaves = new Formula.Logic(identity, FormulaLogicOperator.And,
            new Formula.Logic(halfPlane, FormulaLogicOperator.And, normalization));
        Formula statement = Disp(Seq(
            Forall, Sp, z, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
            disk, Sp, Implies, Sp, positive, Sp, Implies, Sp, leaves, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The completed xi reading in the Mobius coordinate gives the normalized Li-Caratheodory expression.",
            H("Li-Caratheodory Identity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("li-caratheodory-identity"),
                    DeclarationHandle.Create(
                        "D5/S3/Fourier/CompletionConstants/LiCaratheodoryIdentity."
                            + "li_caratheodory_identity"),
                    H("The completed xi reading gives the Li-Caratheodory identity"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a point z in the unit disk and the sourced positive first "
                                + "coefficient, the declaration carries three leaves: the normalized "
                                + "logarithmic-derivative identity, the Mobius image's real-part "
                                + "inequality, and the value one at the origin.")),
                        Paragraph(Text(
                            "The proof uses the completed repository xi reading, Mathlib's "
                                + "logarithmic-derivative composition and constant-factor rules, "
                                + "and the elementary real-part calculation for 1/(1-z). It makes "
                                + "no RH claim and introduces no replacement finite carrier.")),
                    Paragraph(Text(
                        "The first leaf is the boxed formula (274.5). The second and third "
                            + "leaves are the substantive Mobius and normalization bullets "
                            + "immediately following it; the excess-connection bullet is "
                            + "terminological context rather than another proposition.")),
                    Paragraph(Text(
                        "Counting audit: the CAS has three semantic assertions, with no proof "
                            + "section to exclude. The Lean proposition has two binary And nodes "
                            + "and three atomic leaves, in the same order as the three assertions.")),
                    Paragraph(Text(
                        "Carrier audit: z and the norm-defined unit disk are carried by Complex "
                            + "and ‖z‖ < 1; mobiusCoordinate carries 1/(1-z); xiReading is the "
                            + "repository completed xi function; logDeriv carries xi'/xi; lambdaOne "
                            + "and liCaratheodory carry lambda_1 and C_lambda. No abstract or finite "
                            + "replacement carrier is introduced.")),
                    Paragraph(Text(
                        "Search and provenance: repository search found the existing xiReading "
                            + "definition, endpoint values, differentiability, and reflection facts; "
                            + "Mathlib supplied logDeriv_comp, logDeriv_mul_const, Complex normSq, "
                            + "and inverse differentiation. The disk domain is the theorem bullet, "
                            + "and lambda_1 > 0 is the neighboring source equation (270.3). The "
                            + "declaration assumes no RH or other open conjecture."))),
                DescribeRole.Theorem))));
    }
}
