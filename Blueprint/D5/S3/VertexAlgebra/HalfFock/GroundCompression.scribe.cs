using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;
internal sealed class LatticeHalfFockGroundCompressionDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Canonical Ground Compression of the Full Neutral Field",
 H("Canonical Ground Compression of the Full Neutral Field"), Blocks(
 Paragraph(Text("Let D:LatticeData, hu:IsUnit D.G.det, R=Oscillator D, T=ActualGround D hu and M=ActualTensor D hu=R tensor_Complex T. The augmentation epsilon:R -> Complex is precisely the coefficient of the zero oscillator monomial. The canonical linear maps are iota(g)=1 tensor g and pi(r tensor g)=epsilon(r) smul g, using the tensor unit equivalence. No dual vector or scalar moment functional is chosen. All finite inhomogeneous polynomials, zero and one, repeated indices, coincident correction shifts and rank zero remain in scope; no positivity, radius, ground-vector choice or independence assumption is present.")),
 Describe.Lean(DescribeId.Create("canonical-ground-retraction"),
 DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/GroundCompression.ground_retraction"),
 H("Canonical ground retraction"), StatementSource.WithoutFormula(),
 AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
 Blocks(Paragraph(Text("pi composed with iota equals the identity on every actual ground vector. This consumed helper supplies the empty-word case of polynomialField_ground_compression."))), DescribeRole.Theorem),
 Describe.Lean(DescribeId.Create("native-normal-field-ground-augmentation"),
 DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/GroundCompression.polynomialField_ground_compression"),
 H("The full normal field obeys augmentation"), StatementSource.WithoutFormula(),
 AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
 Blocks(
 Paragraph(Text("For every r:R and e:Int, pi composed with (polynomialField D hu 0 r).coeff e composed with iota equals (if e=0 then epsilon(r) else 0) smul id_T. This is an equality of endomorphisms of the entire actual ground module.")),
 Paragraph(Text("In the literal recursive flatCoefficient for index::tail, a negative head mode places jetCurrent on the left. For every tensor v, pi(jetCurrent(index,mode)(v))=0: tensor induction reduces this to epsilon(X_k*r)=0. A nonnegative head places jetCurrent on the right; the actual Gram-weighted annihilation derivation kills the oscillator constant 1. Thus every nonempty flatTerm compresses to zero for arbitrary seed fields, with the original composition order and jet scalars. The existing flatTerm_finite permits pi to pass through the vector-valued finsum. No operator-valued finsum, Wick multiplicativity or commutation of opposite-sign currents is used.")),
 Paragraph(Text("For the empty word, the existing actual zero-charge creation, translation and ground-representation calculation identifies chargedField D hu 0 with the identity field. The identity-field coefficient supplier and pi composed with iota=id give the only surviving monomial. Native polynomial induction and linearity extend this to arbitrary finite r, preserving all multiplicities."))), DescribeRole.Theorem),
 Describe.Lean(DescribeId.Create("full-corrected-neutral-ground-compression"),
 DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/GroundCompression.correctedField_ground_compression"),
 H("Exact Corr vacuum Laurent coefficients of the actual corrected field"), StatementSource.WithoutFormula(),
 AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
 Blocks(
 Paragraph(Text("For every p:R and e:Int, pi composed with (correctedField D hu (Finsupp.single 0 p)).coeff e composed with iota equals the sum, over s in (Corr D 0 p).support, of (if e=-2*s then epsilon((Corr D 0 p)(s)) else 0), acting as a scalar times id_T. The theorem concerns the full corrected field, including its normal term.")),
 Paragraph(Text("Expand the actual correctedField, correctedPolynomial and correctedSum through finite Finsupp.lsum. Apply the public native shiftField coefficient law, which reads exponent e at e+2*s, and then the proved normal-field augmentation law. The physical doubled Hahn exponent is exactly -2*s. The support is contained in the finite image of Corr.support under s -> -2*s, and all odd exponents vanish. These consequences construct compressedLaurent, a finite family whose coefficients are the actual compressed endomorphisms and whose type includes proved odd-coefficient vanishing."))), DescribeRole.Theorem),
 Paragraph(Text("This is a repository derivation of compatibility between native fields and canonical polynomial augmentation, within the classical twisted-lattice construction of Dong-Nagatomo math/9808088v1 section 3.2 and Bakalov-Kac math/0402315v1 section 4.4. The imported implementation retains Kalle Kytola copyright (c) 2025 and the additional half-integer implementation copyright (c) 2026, Apache 2.0. No originality claim is made for classical vacuum compression.")),
 Paragraph(Text("The theorem is coefficientwise and finite after compression. It does not analytically evaluate a general Hahn series or establish completed-operator convergence. Identification with an independently constructed Gaussian determinant, analytic sewing, full twisted VOA/CFT identities, anomaly and fusion structures, string dynamics, spacetime reconstruction and AdS/CFT remain further obligations. A finite Laurent coordinate substitution is separate from these analytic and physical claims.")))));
}
