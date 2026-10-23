using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockSecondSourceTaylorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete current/second-source rational field in the original nested-Q telescope.",
        H("The rational inner field and its two supported orders"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-current-second-source-rational-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_current_second_source_rational_field"),
                H("One rational G_j retains both complete J/B residues and every original label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For the supplied actual homogeneous numerator P at arbitrary natural cutoff K, the theorem constructs G_j(v,z) in the rational field of the two remaining labelled Laurent variables. With M equal to the current/B locality bound, it is the finite sum over alpha<M-j of z^(-alpha) choose(-1/2,alpha) times the local J/B residue of (y-z)^(j+alpha) P/Q_K. No source/source locality witness is required for the caller's K.")),
                    Paragraph(Text("Each numerator monomial is evaluated with its original signed exponents. In the local coordinate h=y-z it has factors (z+h)^e0, h^(j+alpha-M), (z-v+h)^(-L), and the unchanged spectator factor c v^e1 z^e2 (v-z)^(-K). The translated signed powers have nonnegative local Taylor support because z and z-v are nonzero in the coefficient field. The finite binomial coefficient formula is applied to the actual local residue, then summed over the finite support of P.")),
                    Paragraph(Text("The fused residue square identifies both complete inner coefficient maps with the v,z and z,v Hahn expansions of this same G_j. Multiplication by z^(-alpha) precedes expansion and produces the exact shifted mode indices of lastSourceLocalQ. The original four full word orders remain AJB, ABJ, JBA, BJA. Neither remaining variable is specialized to a scalar.")),
                    Paragraph(Text("The contextual Hahn antidiagonal supplies finite support of every outer mode fiber. A finite union over the fractional outer index proves joint finite support of the two actual mode-index summands, and both ordered mode fibers have finite support for every finite outer cutoff. This support comes from the full Hahn expansions and does not assert that an ordered half or a numerator monomial has the complete field's locality cutoff.")),
                    Paragraph(Text("Before distributing the outer readout over the finite numerator expansion, the proof establishes joint finite support over alpha, the numerator exponent, the fractional outer offset and the mode-convolution index for each of the two full orders. The finite-support hypotheses of mathlib's finsum_sum_comm then justify both interchanges. The actual scalar nested-Q value is consequently the explicit finite sum of the complete outer rational readouts of these terms. The local Taylor index inside each signed monomial residue is still in its finite binomial sum.")),
                    Paragraph(Text("For the actual fields A and Bj and their supplied independent locality order H, the complete field is first padded to max(H,L+M+K). The arbitrary-cutoff slice quotient theorem then transports the actual readout to the original P/Q_K. Only after that padding does the finite rational evaluation enter the proof. The theorem retains arbitrary input tensor, functional, signed indices and lifts, zero numerator and empty inner sums; it also transports the complete OuterQCompletion law at H.")),
                    Paragraph(Text("The subsequent actual_second_source_third theorem evaluates these original rational readouts through both ordered Hahn maps. It derives the sharp inner and outer Taylor support, contracts both finite Vandermonde sums and consumes the finite reverse Taylor convolution at t=M-1. The full sameNumeratorCollisionBridge also requires its independent first and middle conjuncts.")),
                    Paragraph(Text("The signed Laurent proof adapts the J/A calculation in LatticeHalfFockOuterTaylorEvaluation to J/B; the Hahn, Laurent and binomial infrastructure is from mathlib under Apache 2.0. The actual supplier closure is inherited research source, including the six additional owners and four modified older owners disclosed with the slice quotient checkpoint. It is not asserted to be an independently integrated dev API. The matching Reg source reconstructs the whole theorem and its positive actual law; the remaining family variation, sensitivity, observational dependence and final registration are unfinished."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-second-source-third"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.actual_second_source_third"),
                H("The original reverse third nested-Q identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For every original lattice, nondegenerate Gram matrix, current label, original source states, natural K, signed lifts and modes, tensor input, linear functional and supplied original homogeneous numerator P, the theorem proves the third equality of sameNumeratorCollisionBridge. The only locality inputs are the original complete A/Bj field orders H3(j). No source/source locality is imposed on K, and no compatible-module or Jacobi premise is added.")),
                    Paragraph(Text("Each actual inner Taylor term is normalized in its unchanged rational coefficient field to signed monomials times (v-z)^(-K-L-k). Its two coefficient maps are the genuine v,z and z,v Hahn expansions. The contextual kernel extraction theorem converts their supported mode convolutions to ordinary binary kernel coefficients. For negative diagonal degree, signed_kernel_choose combines the two origin-mode branches into the integer Laurent binomial coefficient; for nonnegative degree their difference is zero.")),
                    Paragraph(Text("The finite inner index gives alpha+a+k=M-j-1. The original numerator coefficient equation gives e0+e1+e2=degree-n-1, so the surviving outer Taylor index satisfies alpha+a+beta+b=degree and leaves final z exponent -n-1. The full algebraic pole bound fits the padded cutoff max(H3(j),L+M+K). The outer beta/b sum and the inner alpha/a triangle then contract by the two Vandermonde identities, producing exactly epsilon(-L) times the finite collisionTaylor sum for every j. Substitution into the original third telescope and the finite reverse Taylor convolution gives its requested orderedResidueWeight expression.")),
                    Paragraph(Text("Signed numerator exponents, negative signed degree, zero P and all empty finite ranges remain in scope. This is the THIRD conjunct only: the complete sameNumeratorCollisionBridge, VOA program, string theory and AdS/CFT bridges are not established by this theorem. The matching Reg source reconstructs the exact quantified theorem and its actual positive law; four-slot registration remains unfinished under issue 20510."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-inner-taylor-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.secondSourceInnerTaylorTerm"),
                H("The signed inner Taylor summand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("This finite coefficient-field term records the complete signed Laurent factors after the J/B local residue and before either outer Hahn order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("second-source-monomial-taylor-index"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_monomial_taylor_index"),
                H("The finite local Taylor index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The actual signed monomial residue equals its explicit finite local Taylor expansion on every alpha in range M-j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-taylor-inner-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_taylor_inner_expansion"),
                H("The complete signed inner Taylor expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For every alpha in the actual finite range, secondSourceTerm is expanded over the local Taylor index u < M-j-alpha. The expansion retains signed numerator exponents, both pair poles, the spectator factor and the fractional z^(-alpha) shift. The complete G_j is the finite sum over alpha and the actual coefficient support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-reverse-outer-contraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_reverse_outer_contraction"),
                H("Reverse outer contraction after complete local evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For M>0, the theorem consumes the complete signed local evaluation for every original j, applies the finite reverse Taylor convolution at t=M-1, and combines the two epsilon factors. It preserves the signed degree, negative-degree empty branch and ordered residue weight. The actual_second_source_third theorem supplies this local evaluation from the original coefficient-field terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-inner-sharp-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_sharp_support"),
                H("Sharp inner Taylor support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("Every nonempty inner Taylor index satisfies alpha+a+k=M-j-1, including arbitrary signed Laurent numerator exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-inner-vandermonde"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_inner_vandermonde"),
                H("Inner fractional Vandermonde contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The finite -1/2 contraction is proved for every integer Laurent exponent, so negative and zero numerator powers remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-outer-vandermonde"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor.second_source_outer_vandermonde"),
                H("Outer fractional Vandermonde contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The finite -gamma/2 contraction is proved for every integer Laurent exponent and is the outer contraction needed after sharp support."))),
                DescribeRole.Theorem))));
}
