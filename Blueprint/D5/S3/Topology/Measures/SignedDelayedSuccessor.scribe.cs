using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedDelayedSuccessorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-object delayed signed successor",
        H("Same-object delayed signed successor"),
        Blocks(Describe.Lean(DescribeId.Create("delayed-signed-successor"),
            DeclarationHandle.Create("D5/S3/Topology/Measures/SignedDelayedSuccessor.exists_delayed_successor"),
            H("Final source replacement and signed residual births"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The input distinguishes the new row from all old rows. Old I, J and N are defined only on old rows; old labels range over Gamma. Every row has original signed sequences for all old labels and its residual label, with total variation one, support-nullity, regular Jordan parts and positive Jordan mass at least one half. All row maps are continuous and onto, the new row map is injective, and the original support clopens are pairwise disjoint. Old A, B, C, E and every-choice signed F are the only old reference laws. The target row is genuinely old and its target sequence is prescribed Dirac data. Source measures are carried by P, target points by a disjoint clopen Q.")),
                Paragraph(Text("Norm-preserving lifts are selected internally. Old F supplies old references; compact metric weak-star sequential compactness supplies the new row's signed birth clusters. The internally selected equal/distinct delayed split gives increasing auxiliary columns, two infinite source subsets M(e) inside the original source J and N(e), and a clopen separating the full target fibres over y(n). No old J or N is invented for the new row.")),
                Paragraph(Text("The final I(r) contains exactly the auxiliary indices with code(r) less than their column; on the actual target row it is enlarged by M(0) union M(1). The final J equals that source union at the actual source pair and equals the corresponding fixed-label auxiliary range everywhere else. Every genuinely born old N remains unchanged. The new row's old-label reservoirs are its auxiliary fixed-label parity ranges. These same sets satisfy inclusion, disjointness, both infinite parity intersections, exact one-step refinement of old I and J, whole-support old-clopen and new-coordinate fibre constancy, and one common regular signed limit for every lift selection.")),
                Paragraph(Text("Residual initialization follows the final enlargement of I. Actual successor lifts are restricted to that final I, then compact metric weak-star compactness selects a residual J. Its even and odd increasing ranges define two infinite residual reservoirs. Whole-support E transfers the reference limit to every signed lift selection. This covers old row with old label, new row with old label, old row with residual label and the doubly new case. Every even target column retains the strict thirteen forty-eighths and one-sixth signed bounds; odd columns have zero true-sheet mass. The resulting G witness sets are infinite independently of any requirement that they belong to the updated I. Actual norm-preserving lift classes are inhabited at every old and residual label.")),
                Paragraph(Text("This is a local compact metric split construction. Literal ordinal insertion, a compatible transfinite history and the final omega-one carrier require additional constructions. The theorem does not assert an anti-homeomorphism obstruction, the Grothendieck property or the entire signed dual-ball conclusion."))),
            DescribeRole.Theorem))));
}
