using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class ThreeLevelQuantifierSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula transition = F.Id("t");
        Formula readout = F.Id("ell");
        Formula family = F.Id("family");
        Formula compatibleFamily = Call("CompatibleFamilyExists", transition);
        Formula globalSource = Call("GlobalSource", readout, family);
        Formula readoutsCompatible = Call("ReadoutsCompatible", transition, readout);
        Formula finiteBoolFamily = Seq(Call("Fin", D(2)), Sp, Mapsto, Sp, F.Id("Bool"));
        Formula levelThreeToTwo = Disp(Seq(
            readoutsCompatible, Sp, Land, Sp, globalSource, Sp, Rightarrow, Sp,
            compatibleFamily, Dot));
        Formula levelTwoToOne = Disp(Seq(
            compatibleFamily, Sp, Rightarrow, Sp,
            Call("LocalWitnesses", F.Id("Y")), Dot));
        Formula levelOneNotTwo = Disp(Seq(
            Call("LocalWitnesses", finiteBoolFamily), Sp, Land, Sp, Neg, Sp,
            Call("CompatibleFamilyExists", F.Id("twistedTransition")), Dot));
        Formula levelTwoNotThree = Disp(Seq(
            Call(
                "ReadoutsCompatible",
                F.Id("identityTransition"),
                F.Id("constantFalseReadout")),
            Sp, Land, Sp,
            Call("CompatibleFamilyExists", F.Id("identityTransition")),
            Sp, Land, Sp, Neg, Sp,
            Call(
                "GlobalSource",
                F.Id("constantFalseReadout"),
                F.Id("allTrueFamily")),
            Dot));
        Formula premiseNecessary = Disp(Seq(
            Call(
                "GlobalSource",
                F.Id("constantFalseReadout"),
                F.Id("allFalseFamily")),
            Sp, Land, Sp, Neg, Sp,
            Call(
                "ReadoutsCompatible",
                F.Id("twistedTransition"),
                F.Id("constantFalseReadout")),
            Sp, Land, Sp, Neg, Sp,
            Call("CompatibleFamilyExists", F.Id("twistedTransition")),
            Dot));

        const string module =
            "D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite Boolean systems strictly separate local witnesses, compatible families, "
                + "and global sources.",
            H("Three-Level Quantifier Separation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("global-source-implies-compatible-family"),
                    DeclarationHandle.Create(
                        module + "global_source_implies_compatible_family_exists"),
                    H("A compatible global readout supplies a compatible family"),
                    StatementSource.FromAuthor(levelThreeToTwo),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A global source realizes the specified local family. The explicit "
                            + "ReadoutsCompatible premise transports that realization through "
                            + "every all-pairs transition equation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("compatible-family-supplies-local-witnesses"),
                    DeclarationHandle.Create(
                        module + "compatible_family_exists_implies_local_witnesses"),
                    H("A compatible family supplies every local witness"),
                    StatementSource.FromAuthor(levelTwoToOne),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Choosing the simultaneous family already gives one inhabitant in each "
                            + "local type. This implication does not need the compatibility "
                            + "equations after the family has been obtained."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("local-witnesses-do-not-give-compatible-family"),
                    DeclarationHandle.Create(
                        module
                            + "local_witnesses_do_not_imply_compatible_family_exists"),
                    H("Local witnesses need not form a compatible family"),
                    StatementSource.FromAuthor(levelOneNotTwo),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "On Fin 2 with Boolean fibers, every coordinate is inhabited. Identity "
                            + "in one off-diagonal direction and negation in the reverse "
                            + "direction force contradictory equations for any chosen family."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("compatible-family-need-not-have-global-source"),
                    DeclarationHandle.Create(
                        module
                            + "compatible_family_exists_does_not_imply_global_source"),
                    H("A compatible family need not have a global source"),
                    StatementSource.FromAuthor(levelTwoNotThree),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Identity transitions make the all-true Fin 2 Boolean family compatible, "
                            + "while the constant-false readout from the nonempty global carrier "
                            + "Bool cannot realize that family."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("readout-compatibility-is-necessary"),
                    DeclarationHandle.Create(
                        module + "readouts_compatible_is_necessary"),
                    H("Readout compatibility is necessary for the first implication"),
                    StatementSource.FromAuthor(premiseNecessary),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The constant-false family has a global source for the twisted finite "
                            + "system, but those readouts violate its reverse transition and no "
                            + "compatible family exists. Thus the omitted premise cannot be "
                            + "removed from level three implying level two."))),
                    DescribeRole.Theorem))));
    }
}
