using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class TransverseStopLossTomographyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/TransverseStopLossTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite transverse stop-loss profiles satisfy exact transport identities and recover "
            + "their weighted divisor from slope jumps.",
        H("Transverse Stop-Loss Tomography"),
        Blocks(
            DefinitionNode(
                "tail-count",
                "tailCount",
                "Real tail count",
                "The real-valued sum of multiplicities whose transverse distance exceeds the "
                    + "observation depth."),
            DefinitionNode(
                "closed-tail-count",
                "closedTailCount",
                "Closed tail count",
                "The tail count retaining the multiplicity exactly at the observation depth."),
            DefinitionNode(
                "divisor-multiplicity",
                "divisorMultiplicity",
                "Divisor multiplicity",
                "The total multiplicity carried by one transverse distance."),
            DefinitionNode(
                "observation-area",
                "observationArea",
                "Observation area",
                "The remaining-depth loss between omega and omega plus y."),
            Describe.Lean(
                DescribeId.Create("transverse-stop-loss-tomography"),
                DeclarationHandle.Create(Prefix + "transverse_stop_loss_tomography"),
                H("Finite transverse stop-loss tomography"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source's profile is formalized for an arbitrary finite family of "
                            + "transverse distances with natural multiplicities. No positivity "
                            + "assumption on the distances is needed for the transport laws.")),
                    Paragraph(Text(
                        "The tail-count integral is evaluated termwise as the volume of a bounded "
                            + "open interval. Subtracting the two tail integrals gives the swept "
                            + "interval identity, and ordinary derivatives are taken only when "
                            + "both endpoints avoid the finite jump set.")),
                    Paragraph(Text(
                        "The distributional second-derivative formula is represented without a "
                            + "choice of test-function convention: the right slope minus the left "
                            + "slope at every depth is exactly the total divisor multiplicity "
                            + "there. Thus the complete finite transverse divisor is recovered."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Zeros/ObservationDepthStopLoss"))]));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("j");
        Formula carrier = F.Id("J");
        Formula delta = F.DeltaLower;
        Formula multiplicity = F.Id("m");
        Formula omega = F.Omega;
        Formula y = F.Id("y");
        Formula u = F.Id("u");
        Formula x = F.Id("x");
        Formula n = F.Id("N");
        Formula r = F.Id("R");
        Formula area = F.Id("A");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteCarrier = Call("FiniteType", carrier);
        Formula deltaType = Seq(carrier, Sp, To, Sp, real);
        Formula multiplicityType = Seq(carrier, Sp, To, Sp, natural);
        Formula deltaAt = Subscript(delta, index);
        Formula multiplicityAt = Subscript(multiplicity, index);
        Formula far = Seq(omega, Sp, Plus, Sp, y);
        Formula tailAt(Formula depth) => Apply(n, depth);
        Formula remainingAt(Formula depth) => Apply(r, depth);
        Formula areaAt(Formula depth, Formula increment) => Apply(area, depth, increment);
        Formula indicator = Call("indicator", Seq(u, Sp, Lt, Sp, deltaAt));
        Formula tailDefinition = Seq(
            tailAt(u), Sp, Eq, Sp, Sum, Underscore, Grp(index), Sp,
            multiplicityAt, Sp, Cdot, Sp, indicator);
        Formula remainingDefinition = Seq(
            remainingAt(x), Sp, Eq, Sp, Sum, Underscore, Grp(index), Sp,
            multiplicityAt, Sp, Cdot, Sp,
            Call("max", Seq(deltaAt, Sp, Minus, Sp, x), D(0)));
        Formula areaDefinition = Seq(
            areaAt(omega, y), Sp, Eq, Sp, remainingAt(omega), Sp, Minus, Sp,
            remainingAt(far));
        Formula tailIntegral = Call("setIntegral", u, Call("Ioi", omega), tailAt(u));
        Formula intervalIntegral = Call("intervalIntegral", u, omega, far, tailAt(u));
        Formula dY = Subscript(F.Id("partial"), y);
        Formula dOmega = Subscript(F.Id("partial"), omega);
        Formula rightSlope = Call("rightSlope", r, x);
        Formula leftSlope = Call("leftSlope", r, x);
        Formula pointMass = Seq(
            Sum, Underscore, Grp(Seq(deltaAt, Sp, Eq, Sp, x)), Sp, multiplicityAt);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, carrier, Comma, Sp, finiteCarrier, Comma, Sp,
                delta, Colon, Sp, deltaType, Comma, Sp,
                multiplicity, Colon, Sp, multiplicityType, Comma),
            Seq(Forall, Sp, omega, Comma, Sp, y, Colon, Sp, real, Comma, Sp,
                y, Sp, Geq, Sp, D(0), Comma),
            Seq(Open, Forall, Sp, index, Comma, Sp,
                omega, Sp, Neq, Sp, deltaAt, Sp, Land, Sp,
                far, Sp, Neq, Sp, deltaAt, Close, Sp, Rightarrow),
            Seq(tailDefinition, Comma, Sp, remainingDefinition, Comma, Sp, areaDefinition, Comma),
            Seq(remainingAt(omega), Sp, Eq, Sp, tailIntegral, Comma),
            Seq(areaAt(omega, y), Sp, Eq, Sp, remainingAt(omega), Sp, Minus, Sp,
                remainingAt(far), Sp, Eq, Sp, intervalIntegral, Comma),
            Seq(Call("doubleDepthDecay", omega, y), Sp, Eq, Sp, areaAt(omega, y), Comma),
            Seq(Apply(dY, areaAt(omega, y)), Sp, Eq, Sp, tailAt(far), Comma),
            Seq(Apply(dOmega, areaAt(omega, y)), Sp, Eq, Sp,
                tailAt(far), Sp, Minus, Sp, tailAt(omega), Comma),
            Seq(Open, dOmega, Sp, Minus, Sp, dY, Close, Sp,
                areaAt(omega, y), Sp, Eq, Sp, Minus, tailAt(omega), Comma),
            Seq(Forall, Sp, x, Colon, Sp, real, Comma, Sp,
                rightSlope, Sp, Minus, Sp, leftSlope, Sp, Eq, Sp, pointMass, Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Subscript(Formula value, Formula subscript) =>
        new Formula.Subscript(value, subscript);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
