using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid.Connectivity;

internal sealed class CoordinateStreamlineDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition."
            + "exists_coordinate_streamline_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every compact real-interval solenoid path has one compatible coordinate offset family.",
        H("Coordinate Streamline Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("every-coordinate-has-one-compatible-offset-family"),
            DeclarationHandle.Create(Declaration),
            H("Every coordinate shares one compatible offset family"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a nondegenerate interval, the canonical affine homeomorphism transports "
                        + "the path to the unit interval. The frozen interval decomposition then "
                        + "supplies a continuous real lift and one constant element of the visible "
                        + "projection kernel. A singleton interval is transported by the constant "
                        + "unit-interval path, so ordered endpoints cover every nonempty compact "
                        + "real interval.")),
                Paragraph(Text(
                    "The canonical exact-sequence theorem identifies that kernel element with "
                        + "a compatible residue at every positive modulus. Projecting the "
                        + "solenoid reconstruction at an arbitrary modulus gives the displayed "
                        + "circle-coordinate equation for every time.")),
                Paragraph(Text(
                    "The compatible residue family is quantified directly through the existing "
                        + "CongruenceData carrier; no duplicate coordinate or kernel primitive is "
                        + "introduced."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Solenoid/ExactSequence")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Solenoid/IntervalStreamlineDecomposition")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula leftEndpoint = F.Id("a");
        Formula rightEndpoint = F.Id("b");
        Formula interval = Seq(
            OpenBracket, leftEndpoint, Comma, Sp, rightEndpoint, CloseBracket);
        Formula solenoid = F.Id("UniversalSolenoid");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula path = GammaLower;
        Formula lift = F.Id("x");
        Formula offset = F.Id("c");
        Formula modulus = F.Id("m");
        Formula time = F.Id("t");
        Formula continuousPaths = Call("ContinuousMaps", interval, solenoid);
        Formula continuousLifts = Call("ContinuousMaps", interval, reals);
        Formula positiveNaturals = F.Id("PositiveNaturals");
        Formula pathAtTime = Seq(path, Open, time, Close);
        Formula liftAtTime = Seq(lift, Open, time, Close);
        Formula circleClass = Call(
            "circleClass",
            Seq(liftAtTime, Sp, Slash, Sp, modulus));
        Formula embeddedOffset = Call("congruenceEmbedding", offset);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, leftEndpoint, Comma, Sp, rightEndpoint, Colon, Sp,
                reals, Comma, Sp,
                path, Colon, Sp, continuousPaths, Comma),
            Seq(
                leftEndpoint, Sp, Le, Sp, rightEndpoint, Sp, Rightarrow, Sp,
                Exists, Sp, lift, Colon, Sp, continuousLifts, Comma),
            Seq(
                Exists, Sp, offset, Colon, Sp, F.Id("CongruenceData"), Comma, Sp,
                Forall, Sp, modulus, Colon, Sp, positiveNaturals, Comma, Sp,
                time, Colon, Sp, interval, Comma),
            Seq(
                Call("coord", pathAtTime, modulus), Sp, Eq, Sp,
                circleClass, Sp, Plus, Sp,
                Call("coord", embeddedOffset, modulus), Dot),
        ]));
    }
}
