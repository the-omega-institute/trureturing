using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class AlphabetFactorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/AlphabetFactor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous alphabet maps induce compact shift-equivariant factor subshifts.",
        H("Continuous Alphabet Factors of Symbolic Systems"),
        Blocks(
            Paragraph(Text(
                "A continuous map between alphabets acts coordinatewise on full shifts. "
                + "This map is continuous, commutes with every translation shift, and sends a "
                + "compact-alphabet closed subshift to a closed shift-invariant image subshift.")),
            Describe.Lean(
                DescribeId.Create("coordinatewise-alphabet-map"),
                DeclarationHandle.Create(Owner + "alphabetMap"),
                H("Coordinatewise alphabet map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "alphabetMap f x applies f independently at each coordinate of the configuration x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continuous-coordinatewise-map"),
                DeclarationHandle.Create(Owner + "continuous_alphabetMap"),
                H("Continuity of the coordinatewise map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Continuity of f lifts through product projections to continuity of the full-shift map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alphabet-map-shift-factor-law"),
                DeclarationHandle.Create(Owner + "alphabetMap_shift"),
                H("Shift factor law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the alphabet map before or after a translation shift gives the same configuration; "
                    + "alphabetMap_semiconj packages this equality as a semiconjugacy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alphabet-map-semiconjugacy"),
                DeclarationHandle.Create(Owner + "alphabetMap_semiconj"),
                H("Coordinatewise semiconjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each translation parameter, the coordinatewise alphabet map is a semiconjugacy "
                    + "between the source and target full-shift actions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-image-subshift"),
                DeclarationHandle.Create(Owner + "isClosed_image_subshift"),
                H("Closed image of a subshift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A compact source alphabet and Hausdorff target alphabet make the continuous image of a "
                    + "closed subshift compact and therefore closed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("image-shift-invariance"),
                DeclarationHandle.Create(Owner + "mapsTo_image_subshift"),
                H("Shift invariance of the image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shift factor law transports source subshift invariance to the coordinatewise image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mapped-subshift"),
                DeclarationHandle.Create(Owner + "mapSubshift"),
                H("Mapped subshift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "mapSubshift f hf X bundles the closed, shift-invariant image into a FullShift.Subshift "
                    + "over the target alphabet."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mapped-subshift-carrier"),
                DeclarationHandle.Create(Owner + "mapSubshift_carrier"),
                H("Carrier of the mapped subshift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier of mapSubshift is definitionally the coordinatewise image."))),
                DescribeRole.Theorem))));
}
