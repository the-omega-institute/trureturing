using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class FiniteHolonomyEnergyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite stable swap curvature aggregates into a faithful nonnegative energy.",
        H("Finite Holonomy Energy"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-stable-holonomy-energy-bound"),
            DeclarationHandle.Create(
                Prefix + "finite_stable_holonomy_energy_bound"),
            H("Finite Stable Holonomy Energy Bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite carrier, assume every channel has norm at most one and "
                        + "every residual norm is bounded by a common nonnegative envelope. "
                        + "The stable residual holonomy energy is nonnegative and is at most "
                        + "the square of the carrier cardinality times the squared pairwise "
                        + "residual bound.")),
                Paragraph(Text(
                    "The energy is zero exactly when every ordered-pair stable residual swap "
                        + "curvature is zero, and a zero envelope forces zero energy. These "
                        + "claims concern only the finite unnormalized sum; they assert no "
                        + "residual decay, infinite-prime limit, or spectral-energy comparison."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound")),
        ]));

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

    private static Formula Named(Formula name) =>
        Seq(Operatorname, Grp(name));

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula carrier = Iota;
        Formula stable = F.Id("a");
        Formula residual = F.Id("r");
        Formula channel = F.Id("v");
        Formula envelope = Varepsilon;
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula energy = F.Id("E");
        Formula type = Named(F.Id("Type"));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula functionType = new Formula.TypeArrow(carrier, field);
        Formula energyValue = Apply(
            Named(F.Id("stableResidualHolonomyEnergy")), stable, residual, channel);
        Formula residualAtP = Apply(residual, p);
        Formula residualAtQ = Apply(residual, q);
        Formula channelAtP = Apply(channel, p);
        Formula channelAtQ = Apply(channel, q);
        Formula curvature = Apply(
            Named(F.Id("stableResidualSwapCurvature")),
            stable, residualAtP, residualAtQ, channelAtP, channelAtQ);
        Formula stableGap = Seq(Open, stable, Sp, Minus, Sp, D(1), Close);
        Formula pairwiseBound = Seq(
            D(2), Sp, Times, Sp, new Formula.Norm(stableGap),
            Sp, Times, Sp, envelope,
            Sp, Plus, Sp,
            D(2), Sp, Times, Sp, envelope, Caret, Grp(D(2)));
        Formula realCardinality = new Formula.Subscript(
            Named(F.Id("card")), reals);
        Formula carrierSquare = Seq(
            Apply(realCardinality, carrier), Caret, Grp(D(2)));
        Formula energyBound = Seq(
            carrierSquare, Sp, Times, Sp,
            Open, pairwiseBound, Close, Caret, Grp(D(2)));
        Formula channelBound = Seq(
            Forall, Sp, p, Colon, Sp, carrier, Comma, Sp,
            new Formula.Norm(channelAtP), Sp, Leq, Sp, D(1));
        Formula residualBound = Seq(
            Forall, Sp, p, Colon, Sp, carrier, Comma, Sp,
            new Formula.Norm(residualAtP), Sp, Leq, Sp, envelope);
        Formula premises = Seq(
            D(0), Sp, Leq, Sp, envelope,
            Sp, Land, Sp, Open, channelBound, Close,
            Sp, Land, Sp, Open, residualBound, Close);
        Formula zeroCriterion = Seq(
            energy, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Forall, Sp, p, Comma, Sp, q, Colon, Sp, carrier, Comma, Sp,
            curvature, Sp, Eq, Sp, D(0));
        Formula zeroEnvelope = Seq(
            envelope, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            energy, Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, field, Colon, Sp, type, Comma, Sp,
            carrier, Colon, Sp, type, Comma, Sp,
            OpenBracket, Named(F.Id("NormedField")), Open, field, Close, CloseBracket,
            Comma, Sp,
            OpenBracket, Named(F.Id("Fintype")), Open, carrier, Close, CloseBracket,
            Comma, RowBreak, Grp(),
            stable, Colon, Sp, field, Comma, Sp,
            residual, Colon, Sp, functionType, Comma, Sp,
            channel, Colon, Sp, functionType, Comma, Sp,
            envelope, Colon, Sp, reals, Comma,
            RowBreak, Grp(),
            Open, premises, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            energy, Sp, Colon, Eq, Sp, energyValue, Comma,
            RowBreak, Grp(),
            Open,
            D(0), Sp, Leq, Sp, energy, Sp, Land,
            RowBreak, Grp(),
            energy, Sp, Leq, Sp, energyBound, Sp, Land,
            RowBreak, Grp(),
            Open, zeroCriterion, Close, Sp, Land,
            RowBreak, Grp(),
            Open, zeroEnvelope, Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
