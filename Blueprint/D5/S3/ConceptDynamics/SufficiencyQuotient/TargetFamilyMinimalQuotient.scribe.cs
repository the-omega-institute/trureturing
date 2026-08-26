using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SufficiencyQuotient;

internal sealed class TargetFamilyMinimalQuotientDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient."
            + "target_family_minimal_quotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simultaneous target-kernel quotient is the coarsest state sufficient "
            + "for every member of a dependent target family.",
        H("Minimal Quotient for a Target Family"),
        Blocks(Describe.Lean(
            DescribeId.Create("target-family-minimal-quotient"),
            DeclarationHandle.Create(Declaration),
            H("The target-family quotient is minimally sufficient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is arbitrary, the target output type may depend on its "
                        + "index, and the joint readout is the repository's canonical "
                        + "dependent product of all target values.")),
                Paragraph(Text(
                    "The quotient is taken by equality of that joint readout. Its canonical "
                        + "projection admits a unique descended readout for every target, so "
                        + "the quotient itself decides the whole target family.")),
                Paragraph(Text(
                    "If another readout decides every target, equality under that readout "
                        + "forces equality of the complete target profile. Its kernel is "
                        + "therefore contained in both the profile kernel and the kernel of "
                        + "the canonical quotient projection."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula targetFamily = F.Id("Y");
        Formula targets = F.Id("K");
        Formula readout = F.Id("q");
        Formula index = F.Id("i");
        Formula factor = F.Id("factor");
        Formula descend = F.Id("descend");
        Formula profile = Call("jointReadout", targets);
        Formula quotient = Call("Quotient", Call("ker", profile));
        Formula projection = Call("quotientClassMap", profile);
        Formula indexedOutput = Apply(targetFamily, index);
        Formula target = Apply(targets, index);
        Formula targetType = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Arrow(stateType, indexedOutput));
        Formula sufficient = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Exists, Sp, Typed(factor, Arrow(outputType, indexedOutput)), Comma, Sp,
            target, Sp, Eq, Sp, Call("compose", factor, readout));
        Formula uniqueDescent = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Exists, Bang, Sp,
            Typed(descend, Arrow(quotient, indexedOutput)), Comma, Sp,
            target, Sp, Eq, Sp, Call("compose", descend, projection));
        Formula conclusion = Seq(
            OpenBracket,
            Open, uniqueDescent, Close, Sp, Land, RowBreak, Grp(),
            Call("ker", readout), Sp, Subseteq, Sp, Call("ker", profile),
            Sp, Land, RowBreak, Grp(),
            Call("ker", readout), Sp, Subseteq, Sp, Call("ker", projection),
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, stateType, Comma, Sp, outputType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(targetFamily, Arrow(indexType, TypeUniverse())), Comma, Sp,
            Typed(targets, targetType), Comma, RowBreak, Grp(),
            Typed(readout, Arrow(stateType, outputType)), Comma, RowBreak, Grp(),
            Open, sufficient, Close, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
