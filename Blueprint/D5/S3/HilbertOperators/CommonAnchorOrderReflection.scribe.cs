using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class CommonAnchorOrderReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/CommonAnchorOrderReflection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of complex linear actions sharing a nonzero source anchor admits one simultaneous decoder exactly when its positive sandwich average reflects positive semidefiniteness. The decoder is a mathematical linear readout; physical preparation, control and execution are separate obligations.",
        H("Common-anchor order reflection"), Blocks(
            Describe.Lean(DescribeId.Create("common-anchor-sandwich"),
                DeclarationHandle.Create(Prefix + "sandwich"), H("The original weighted sandwich map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary finite-dimensional complex Hilbert spaces E and F, a finite nonempty active index type S, and complex linear actions V(l): E to F, the map T sends an operator X to the sum of p(l) V(l) X V(l)*. The theorem uses strictly positive real weights whose sum is one. Individual actions need not be injective, and their common anchor image is allowed to be zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-anchor-reflection"),
                DeclarationHandle.Create(Prefix + "common_anchor_order_reflection"), H("Four equivalent conditions and exact compression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Fix any nonzero e in E and any v in F such that V(l)e=v for every active l. The theorem identifies: reflection of PSD on every Hermitian X; rejection of I-(1+eta)|x><x| for every unit vector x and every real eta>0; existence of a single complex linear C satisfying CV(l)=I for all l; and inclusion of the kernel of (x(l)) |-> sum V(l)x(l) in the kernel of (x(l)) |-> sum x(l). Every such decoder satisfies C T(X) C*=X on the whole operator space, hence on its Hermitian part. T also preserves PSD.")),
                    Paragraph(Text("The necessity proof first obtains a nonzero joint adjoint ray. If the stacked perpendicular adjoint map had its kernel contained in the kernel of the stacked full adjoints, finite-dimensional linear factorization would give a squared norm bound. Its reciprocal supplies a strictly positive eta for which the forbidden rank-one test is PSD. Consequently a joint ray exists. Pairing it with the common anchor forces every component coefficient to agree, and at least one nonzero component makes that common coefficient nonzero.")),
                    Paragraph(Text("Pairing a synthesis relation with these rays shows that its coordinate sum is orthogonal to every unit direction not orthogonal to e. Normalization extends this to all nonorthogonal vectors. The vectors e and x+e cover the remaining orthogonal directions by subtraction, so the coordinate sum vanishes. Quotient factorization and extension give C. This argument retains the zero-common-image case and all noninjective components; it assumes no decoder, coefficient agreement or kernel compatibility.")),
                    Paragraph(Text("This is the finite-dimensional common-anchor theorem 85.2 from the repository's Quantum Origin volume V. In the pure three-leg consumer, E is the Hilbert–Schmidt matrix space, V(l)H is the action of H on leg l of the original pure vector, and e is the identity matrix. The theorem supplies the order-reflection and common-decoder criterion for that family. Identifying the event output with its Choi sandwich, all-sector CP certification, probe preparation and event-source contracts remain separate results. No physical channel interpretation of C is asserted."))), DescribeRole.Theorem))));
}
