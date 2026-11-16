using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetZhuRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full actual Zhu algebra acts on the entire dual-coset bottom",
        H("The full actual Zhu algebra acts on the entire dual-coset bottom"),
        Blocks(
            Paragraph(Text("Let D be the original lattice data of arbitrary natural rank, with symmetric integral Gram matrix G and even diagonal, and assume its real Gram matrix is positive definite. Let beta be an integral charge and mu a rational vector satisfying sum_j G(i,j) mu(j) = beta(i) for every i. Every result here uses these original parameters and the original module action(D,beta). Bottom is the entire rational energy fiber at the attained global minimum of one half of (gamma+mu)^T G (gamma+mu), including all minimizing charges. Rank zero and the rank-one half-shift bottom with two independent eigenvectors are retained; there is no determinant-unit, positive-rank, norm-four or one-dimensional-bottom restriction.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-zero-mode-circle"),
                DeclarationHandle.Create(Prefix + "zeroMode_circle"),
                H("Every original full circle generator acts by zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural p, homogeneous original a of weight p and unrestricted original b, the zero mode of NormFourZhuFinite.circle(D,p,a,b) vanishes. Despite the supplier's name, this circle is the full binomial sum of choose(p,j) times the actual mode mu(a,j-2,b), with no norm-four restriction on a or b. In the consumed private circle_homogeneous proof, actual mode grading identifies its zero-mode indices as p+q-j. Core.circle_residue_top is applied to module_fullLaw derived from the original module Borcherds and to high_mode_kills_bottom for both inputs. The latter discharges the actual bottom truncations from energy minimality. Decomposing the unrestricted second state into its existing finite nonnegative gradeProjection sum extends the homogeneous residue identity to every b. This is the residue argument used for annihilation of the literal span, not an assumed circle-action law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-zhuo-le-kernel"),
                DeclarationHandle.Create(Prefix + "zhuO_le_kernel"),
                H("The literal full O is contained in the zero-mode kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Submodule.span_le extends zeroMode_circle to ActualZhuFinite.zhuO(D), the existing span of all full circle generators with unrestricted second state. The conclusion is O <= ker(zeroMode). It proves neither kernel equality nor faithfulness, and does not define O by a representation kernel. The representation descends this linear map by the proved kernel containment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-zero-mode-star"),
                DeclarationHandle.Create(Prefix + "zeroMode_star"),
                H("Multiplication of zero modes for all original states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For unrestricted original a,b, zeroMode(star(a,b)) equals zeroMode(a) times zeroMode(b), with multiplication in Module.End given by composition. The consumed private star_homogeneous_zeroMode uses the existing star_homogeneous expansion and actual grading to obtain indices p+q-1-j. Core.star_residue_top consumes the derived original-module fullLaw and both minimal-energy high-mode vanishings, yielding the composition identity. The existing finite energy decompositions of both original states, complex linearity and the finite product-of-sums identity extend this result to every state. Product compatibility is proved; it is not supplied by an assumed algebra action. The generic residue suppliers and the converted interfaces are reused, rather than independently published as new helpers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-zero-mode-vacuum"),
                DeclarationHandle.Create(Prefix + "zeroMode_vacuum"),
                H("The original vacuum acts as the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vacuum is in grade zero. zeroMode_homogeneous and the original module_vacuum identity field identify its coefficient minus one with the identity on the full bottom. The representation uses this identity as its unit law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-representation"),
                DeclarationHandle.Create(Prefix + "representation"),
                H("A unital complex algebra homomorphism from the original Zhu quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Using the existing ActualZhuAlgebra.quotientRing and quotientAlgebra, representation is an AlgHom from Q(D) = Carrier(D) modulo ActualZhuFinite.zhuO(D) to End_C(Bottom). The original quotient linear lift is justified by zhuO_le_kernel. AlgHom.ofLinearMap uses the proved vacuum unit and zeroMode_star; quotient surjectivity and quotientProduct_mk reduce multiplication to original representatives. The two ideal stabilities and quotient associativity are already proved suppliers of ActualZhuAlgebra, not new premises. This is the actual descended action on the same carrier quotient and literal O."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhurepresentation-representation-mk"),
                DeclarationHandle.Create(Prefix + "representation_mk"),
                H("Full-family evaluation on original homogeneous representatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer k, every original a in grade k and every v in the full bottom, the underlying carrier vector of representation([a])(v) equals the coefficient k-1 of the original module field action(a) applied to v. This evaluation theorem retains the entire original parameter telescope; zeroMode_homogeneous supplies this evaluation identity for the constructed action."))),
                DescribeRole.Theorem),
            Paragraph(Text("The residue construction follows Zhu/Frenkel--Zhu mathematics and the source-faithful Lean adaptation of Fedor K. Popov, Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean and VOA/Modules/ZeroModeMult.lean, Apache-2.0. The native Core residue calculus, Mathlib quotient descent, actual fields, module Borcherds and energy suppliers retain their existing ownership. ActualZhuJointFaithful evaluates this representation on the complete native minimum basis, proves joint injectivity directly from its scalar matrix coefficients and obtains the sharp dimension equality. Nontriviality and finite dimension of the bottom are supplied by the original bottom_eigenvector, moduleL_eigen_iff and all_eigenspaces_finiteDimensional theorems. No irreducibility or rationality hypothesis is used.")))));
}
