using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class NativePSDModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire native PSD real dual and mixed exclusion geometry supplies a complete original EB3 regular-anchor qutrit inhabitant.",
        H("The full native PSD family and qutrit model"),
        Blocks(
            Paragraph(Text("Let J be any finite type with decidable equality. H is the real normed space HermitianMat J C with its trace inner product and Frobenius norm. The cone is every positive semidefinite element of H, and the unit is the real trace. A real linear functional on all of H is an effect candidate. Properness bounds it between zero and the unit on every unnormalized positive matrix. The normalized base and the pure set retain the definitions of CircuitBalancedConfirmation; mixed exclusions and common effects retain the definitions of FacetZeroGluing and OrthogonalJointCompletion.")),
            Entry("entire-native-cone", "cone", "The entire native PSD cone", DescribeRole.Definition,
                "For every J, cone is PointedCone.positive R H, with membership exactly X PSD. Its name supplies no additional salience hypothesis."),
            Entry("real-trace-unit", "unit", "The real trace unit", DescribeRole.Definition,
                "For every J and X in H, unit(X)=Re tr(X). It is the linear trace pairing with the identity matrix."),
            Entry("entire-real-dual", "effect", "Trace-pairing effects", DescribeRole.Definition,
                "For every J and Hermitian E, effect(E) is the real linear map X to Re tr(EX) on the entire H. Finite dimensional Riesz representation gives every real linear functional this form, uniquely. PSD self-duality makes properness equivalent to zero <= E <= I. No subset of real linear effects is selected."),
            Entry("confirmed-projection-domination", "confirming_dominates", "A confirming contraction dominates its projection", DescribeRole.Theorem,
                "For every J, every v in EuclideanSpace C J with norm(v)=1, and every E in H, if E is PSD, E <= I and Re tr(E vv*)=1, then vv* <= E. Writing P=vv*, PSD zero pairing gives (I-E)P=0 and its adjoint P(I-E)=0. The original Hermitian block (I-P)E(I-P) is therefore E-P, and PSD congruence proves the inequality. The proof includes all finite dimensions and singular effects. It imposes no selected effect menu or additional model premise."),
            Entry("whole-mixed-exclusion", "whole_mixed_exclusion", "The entire mixed exclusion face", DescribeRole.Theorem,
                "For every J and unit vector v in EuclideanSpace C J, exclusion(cone,unit,vv*) equals exactly the set of all Hermitian X with X PSD, trace(X)=1 and Re tr(vv*X)=0. The exclusion on the left uses the existence of an arbitrary confirming real linear functional on all of H. Riesz representation and PSD self-duality turn that functional into a positive contraction E. Confirming domination and PSD trace monotonicity force the zero projection reading. In the reverse direction the projection pairing itself supplies an actual proper confirming effect. Both directions include every normalized mixed state."),
            Entry("whole-common-uniqueness", "whole_common_unique", "Uniqueness in the full real dual", DescribeRole.Theorem,
                "For every J with card(J)>1, every unit vector v in EuclideanSpace C J and every real linear functional f on all of H, common(cone,unit,vv*,f) holds if and only if f=effect(vv*). The normalized complement (I-vv*)/(card(J)-1) belongs to the entire original exclusion. Vanishing there forces the representing positive contraction E to have trace one. The existing original pairing-one uniqueness theorem then identifies E with vv*. The converse uses the whole mixed exclusion equality. No uniqueness is assumed, and the effect domain is the full real linear dual."),
            Entry("whole-original-pure-carrier", "native_pure_iff", "The original pure carrier", DescribeRole.Theorem,
                "For every finite J and every Hermitian X, X belongs to the original pure(cone,unit) if and only if X=vv* for some unit vector v in EuclideanSpace C J. The original pure set consists of real extreme points of the entire normalized PSD base. PSD square root columns give a finite nonzero rank one decomposition of every positive matrix, establishing the actual ROG premise of the existing SectionROGFrame.whole_pure_carrier. That frozen theorem supplies the extreme point characterization; no selected pure menu is used."),
            Entry("whole-exclusion-label-injectivity", "native_exclusion_injective", "Exclusions identify every original pure label", DescribeRole.Theorem,
                "For every finite J with card(J)>1, the map from every original pure point p to its entire mixed exclusion set is injective. The normalized complement of one projection lies in its exclusion; equality of exclusions makes its pairing with the other projection zero. The existing original pairing-one uniqueness theorem identifies the two unit trace projections. This is injectivity on the complete original extreme point carrier."),
            Paragraph(Text("For the model construction specialize J to Fin 3, so V=H is the full real space of complex Hermitian three by three matrices. The anchor projection is diag(1,0,0). The all-pure EB3 and complete original-family existence results below assert this qutrit instance; the preceding effect, pure-carrier and exclusion results apply to every finite J under their stated hypotheses.")),
            Describe.Lean(DescribeId.Create("native-first-vector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/NativePSDModel.vzero"),
                H("The first native coordinate vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("vzero is the vector (1,0,0) in EuclideanSpace C (Fin 3)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-first-unit-vector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/NativePSDModel.vzero_unit"),
                H("The concrete anchor vector has unit norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The norm of vzero is one. This consumed helper fixes the actual original pure anchor and permits the all-pure unitary chart construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-anchor-chart"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/NativePSDModel.anchorChart"),
                H("The full affine Bloch chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let r=(x,y,z) range over the entire EuclideanSpace R (Fin 3). Define beta(r)=1/2 [[1+z,x-iy],[x+iy,1-z]], and embed beta(r) as the lower two by two block of a three by three matrix with zero first row and column. This defines an affine map injective on the whole three-space. Its image of the closed unit ball is exactly the entire mixed exclusion of the first projection. Existing Bloch PSD and reconstruction results give beta(r) PSD exactly when norm(r)<=1. Conversely, zero projection pairing for a positive qutrit forces the first row and column to vanish by the PSD zero quadratic form criterion. Compression then recovers every excluded density matrix, including all mixed and singular boundary states."))),
                DescribeRole.Definition),
            Entry("all-pure-full-charts", "native_EB3", "Full three-ball charts at every original pure label", DescribeRole.Theorem,
                "EB3 C u holds. For every p in the original pure set, native_pure_iff supplies p=vv* with norm(v)=1. Extend v to a complex orthonormal basis and form the actual unitary matrix U whose first column is v. Congruence X to UXU* transports the entire anchor chart. Its inverse is congruence by U*. Positivity, real trace and the projection pairing are invariant under this same unitary. The resulting real affine parameterization is injective on the entire three-space, and its closed unit ball image equals the entire original mixed exclusion of p. No selected pure labels, effects or mixed states enter the construction."),
            Entry("complete-original-family-inhabitant", "original_family_inhabited", "A complete original-family inhabitant and exact endpoint application", DescribeRole.Theorem,
                "There exist an actual original pure point p, a real linear functional e on all of V and a FullBall3Chart a of p such that C is closed; u(X)>0 for every nonzero X in C; span_R C=V; EB3 C u holds for all original pure labels; the original exclusion map is injective on all original pure labels; e is common at p in the full original real dual; and Regular C u p holds. Moreover there exists n:NativeChart C u p e a satisfying ContactCriterion n. Concretely p is diag(1,0,0), e(X)=Re X00 and a embeds the full two by two Bloch ball in the lower block. Closedness and strict positive trace use the existing Hermitian PSD order; positive and negative parts prove generation. The entire mixed exclusion correspondence and its complement state prove full exclusion injectivity and common-effect uniqueness. Applying regular_anchor_contact_criterion to these actually proved premises gives width(a)=1 iff minimum(n)=1 iff the closed unit three-ball meets frontier(shell(n)); when minimum(n)>1 it also gives minimum(n) times that ball contained in shell(n), the unit ball contained in its interior, and boundaryDistance(n)>=minimum(n)-1>0. The endpoint is conditional in general, but this existential model attestation discharges every original premise with a concrete Lean construction."),
            Paragraph(Text("The construction proves mathematical domain inhabitance of this native instance. It asserts neither an original-model strict delta greater than one instance nor empirical physical realization. It does not change the scope or premises of the original general contact theorem. Matrix positivity, the trace inner product, PSD self-duality, pure-carrier and Bloch results are reused from their existing sources. Literature priority is not asserted.")))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title,
        DescribeRole role, string text) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/NativePSDModel." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
