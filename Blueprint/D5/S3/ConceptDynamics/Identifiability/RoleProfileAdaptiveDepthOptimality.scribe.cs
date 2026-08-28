using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class RoleProfileAdaptiveDepthOptimalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Identifiability/RoleProfileAdaptiveDepthOptimality."
            + "independent_role_profile_adaptive_depth_optimality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent binary role profiles require and admit exactly one experiment per role.",
        H("Adaptive Depth of Independent Role Profiles"),
        Blocks(Describe.Lean(
            DescribeId.Create("independent-role-profile-adaptive-depth-optimality"),
            DeclarationHandle.Create(Declaration),
            H("The role-profile depth bound is attained by coordinate experiments"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state carrier contains every Boolean profile on r role coordinates. "
                        + "A deterministic adaptive binary protocol identifies a profile only "
                        + "when equal transcripts force the underlying profiles to agree.")),
                Paragraph(Text(
                    "The general binary-protocol bound therefore forces at least r rounds. "
                        + "Jointly reading the r coordinate projections is injective, giving "
                        + "a nonadaptive role-basis experiment at the same depth."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rank = F.Id("r");
        Formula depth = F.Id("d");
        Formula protocol = F.Id("pi");
        Formula profile = F.Id("p");
        Formula coordinate = F.Id("i");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula profileCarrier = Seq(
            Call("Fin", rank), Sp, To, Sp, F.Id("Bool"));
        Formula constantObservation = Grp(
            profile, Sp, Mapsto, Sp, F.Id("unit"));
        Formula coordinateReadout = Grp(
            coordinate, Sp, Mapsto, Sp,
            Grp(profile, Sp, Mapsto, Sp,
                profile, Open, coordinate, Close));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, rank, Sp, InMacro, Sp, naturalNumbers, Comma),
            Seq(
                Open, Forall, Sp, depth, Sp, InMacro, Sp, naturalNumbers,
                Comma, Sp, protocol, Colon, Sp,
                Call("BinaryProtocol", profileCarrier, depth), Comma, Sp,
                Call("IdentifiesGiven", constantObservation, F.Id("id"), protocol),
                Sp, Implies, Sp, rank, Sp, Leq, Sp, depth, Close,
                Sp, Land),
            Seq(
                Call("Injective", Call("jointReadout", coordinateReadout)), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
