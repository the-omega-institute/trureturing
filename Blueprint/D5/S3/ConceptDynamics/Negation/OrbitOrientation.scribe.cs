using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class OrbitOrientationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Negation/OrbitOrientation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readouts hide or expose free involutions; Boolean orientations are transversals.",
        H("Orbit Orientation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-orbit-pairs-have-exactly-one-local-mode"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "boolean_orbit_exactly_one"),
                H("A Boolean orbit pair has exactly one local mode"),
                StatementSource.FromAuthor(ExactlyOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a chosen orbit point, a Boolean readout either agrees with its value "
                            + "on the paired point or equals the Boolean negation of that value.")),
                    Paragraph(Text(
                        "The two alternatives cannot hold together, because no Boolean value "
                            + "equals its own negation. This is a local dichotomy and does not "
                            + "claim that one mode is chosen uniformly on all orbits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negating-readouts-are-exactly-transversal-supports"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "negatingReadout_iff_trueSupport_transversal"),
                H("Negating readouts are exactly transversal supports"),
                StatementSource.FromAuthor(TransversalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A globally negating Boolean readout changes truth value at every paired "
                            + "point. Its true support therefore contains exactly one side of each "
                            + "involutive orbit.")),
                    Paragraph(Text(
                        "Conversely, if the true support is an orbit transversal, membership and "
                            + "nonmembership alternate across every pair. Exhausting the four "
                            + "Boolean value combinations yields the negating equation."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula ExactlyOneFormula()
    {
        Formula state = F.Id("X");
        Formula negation = F.Id("negation");
        Formula readout = F.Id("readout");
        Formula x = F.Id("x");
        Formula atX = Call("readout", readout, x);
        Formula atNegated = Call("readout", readout, Call("neg", negation, x));
        Formula equalCase = Seq(atNegated, Sp, Eq, Sp, atX);
        Formula negatedCase = Seq(
            atNegated, Sp, Eq, Sp, Call("not", atX));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, negation, Colon, Sp,
            Call("InvolutiveNegation", state), Comma, RowBreak, Grp(),
            readout, Colon, Sp, Arrow(state, F.Id("Bool")), Comma, Sp,
            x, Colon, Sp, state, Comma, RowBreak, Grp(),
            Open, equalCase, Sp, Lor, Sp, negatedCase, Close,
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open, equalCase, Sp, Land, Sp, negatedCase, Close,
            Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TransversalFormula()
    {
        Formula state = F.Id("X");
        Formula negation = F.Id("negation");
        Formula readout = F.Id("readout");

        return Disp(Seq(
            Forall, Sp, negation, Colon, Sp,
            Call("InvolutiveNegation", state), Comma, Sp,
            readout, Colon, Sp, Arrow(state, F.Id("Bool")), Comma, RowBreak, Grp(),
            Call("NegatingReadout", negation, readout), Sp, Iff, Sp,
            Call(
                "OrbitTransversal",
                negation,
                Call("trueSupport", readout)),
            Dot));
    }
}
