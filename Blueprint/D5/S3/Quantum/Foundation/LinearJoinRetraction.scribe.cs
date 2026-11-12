using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class LinearJoinRetractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive trace-subunital retractions and full proper-effect transport across a real linear join.",
        H("Linear join retractions and effect transport"),
        Blocks(
            Paragraph(Text("Let A be a finite dimensional real normed vector space with a pointed cone C and a linear unit u. A JoinData record specifies left and right subspaces U and W, their entire overlap S, a topological linear join U sup W = A, and overlap projections that fix S. The side cone is the exact comap of C along the subspace inclusion and the side unit is u restricted along that inclusion. No finite-pure, identity-membership, or selected-effect assumption is part of this interface.")),
            Describe.Lean(DescribeId.Create("side-cone"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.sideCone"),
                H("The cone on a supported side"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("sideCone C U contains exactly the vectors of U whose ambient inclusion lies in the original cone C."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("side-unit"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.sideUnit"),
                H("The inherited unit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("sideUnit u U is the original linear unit composed with the inclusion of U into A."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("join-data"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.JoinData"),
                H("An entire linear join with overlap projections"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("JoinData records U, W and their equality S=U intersect W, the whole join U sup W=A, and projections W to S and U to S that are the identity on the overlap. The projection equalities make the two glued retractions independent of decompositions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("proper-effect-interval"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.properEffect"),
                H("The full original proper-effect interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("properEffect packages every real linear functional satisfying 0 <= f(x) <= u(x) for every x in the entire original cone."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("side-proper-effect-interval"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.sideProperEffect"),
                H("A side proper-effect interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("sideProperEffect is the same full proper interval on the exact side cone and inherited side unit."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effect-restriction"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.restrictEffect"),
                H("Restrict a full original proper effect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("restrictEffect composes an original proper effect with the side inclusion, retaining the full pointwise bounds on every side-cone element."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("g2"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.G2"),
                H("The full proper-effect midpoint law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("G2 quantifies over every pure reference p and pure q,r. Different full proper confirming effects may witness p perpendicular q and p perpendicular r, while one confirming proper effect must vanish at the midpoint (q+r)/2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("left-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.RetractionCertificate"),
                H("ROG support certificate for the left side"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A RetractionCertificate gives a generator set for the original cone, proves every generator is sent by the left retraction back into C, proves the inherited unit does not increase on generators, and lifts every side pure point to an original pure point with the same ambient vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("right-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.RightRetractionCertificate"),
                H("ROG support certificate for the right side"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("RightRetractionCertificate supplies the symmetric generator, positivity, subunit and pure-lift data for W."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("left-supported-cone"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft"),
                H("The left supported cone as a retraction image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("supportedConeLeft is the image of the original generating hull under the left retraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("right-supported-cone"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight"),
                H("The right supported cone as a retraction image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("supportedConeRight is the symmetric image of the original generating hull under the right retraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("left-supported-cone-equality"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft_eq_sideCone"),
                H("Exact left supported-cone equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The image of the full original generating hull under the left retraction equals the exact ambient cone comapped to U. This is the abstract ROG form of the supported PSD intersection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-supported-cone-equality"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight_eq_sideCone"),
                H("Exact right supported-cone equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The right retraction image of the full original generating hull equals the exact cone cut down to W."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-extension"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_left"),
                H("Extend every left proper effect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every proper effect on the complete left side extends by composition with the left retraction to a proper effect on all of C. The proof propagates generator bounds through the conic hull and preserves the inherited unit inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-extension"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_right"),
                H("Extend every right proper effect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The corresponding composition with the right retraction extends every proper effect on W to the full original interval."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-surjectivity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_left"),
                H("Full effect restriction is onto on the left"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Restriction of the entire original proper-effect interval to U is surjective. The extension is the left proper effect composed with the positive retraction and restricts back exactly on U."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-surjectivity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_right"),
                H("Full effect restriction is onto on the right"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Restriction of the entire original proper-effect interval to W is likewise surjective, with the right retraction as the extension map."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_left"),
                H("Exact left comparison correspondence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every left pure reference and every left vector, the infimum over the complete side proper-effect interval equals the original comparison at the ambient vectors. Restriction and retraction extension identify the two confirming-effect value sets exactly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_right"),
                H("Exact right comparison correspondence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The same equality of full confirming-effect value sets holds on W for every right pure reference and every right vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("left-g2-inheritance"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_left"),
                H("G2 inheritance on the left"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If the original carrier satisfies G2, the left side satisfies G2 using its complete proper-effect interval. Side witnesses extend to original witnesses, the original common midpoint witness is restricted back, and the pure-lift clauses preserve every pure and mixed quantifier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-g2-inheritance"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_right"),
                H("G2 inheritance on the right"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The same argument transports G2 to W with the full right proper-effect interval and the right pure-lift certificate."))), DescribeRole.Theorem))));
}
