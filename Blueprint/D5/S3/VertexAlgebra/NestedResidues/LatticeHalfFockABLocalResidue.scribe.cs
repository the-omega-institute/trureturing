using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockABLocalResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete source/source local residues in the original nested-Q coordinates.",
        H("Complete A/B Laurent residues"),
        Blocks(
            Paragraph(Text("The original variable labels are y=J, v=A, z=B. The finite ternary Laurent numerator is P and its denominator is (y-v)^L (y-z)^M (v-z)^K. All numerator exponents and collision weights are signed. The source/source local coordinate is v=z+t; y remains a spectator. Complete local rational residues are formed before the finite monomial expansion. These results establish local rational dependencies of the middle actual-Q equation; the actual finite-qField identification, complete joint outer support and final same-numerator Taylor equation remain additional obligations.")),
            Describe.Lean(
                DescribeId.Create("ab-complete-remaining-orders"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_remaining_orders"),
                H("Signed A/B residue and both complete remaining orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("A signed monomial has local factors (z+t)^b and (y-z-t)^(-L), together with the unchanged independent pole (y-z)^(-M) and local power t^(w-K). The existing signed Laurent-pair residue theorem evaluates its complete residue on the finite antidiagonal u+v=K-w-1. For w at least K the residue is zero. Summing the original finite numerator support retains zero polynomials, negative total degrees and all signed spectators.")),
                    Paragraph(Text("The complete binary rational G is the finite fractional sum of these ordinary residues, each multiplied by the original Laurent mode shift z^(-ell). Its two remaining Hahn orders are [y,z] and [z,y]. Their exact coefficients give the two source/source lastSourceLocalQ values, with independent fractional cutoff I. No unsupported infinite interchange or locality assertion on a monomial is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-ab-local-cutoff-compat"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.actual_ab_local_cutoff_compat"),
                H("Compatibility of complete local fractional cutoffs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("Arbitrary supplied actual homogeneous numerators P,K and P1,K1 define the same rational quotient by actual_slice_quotient_compat. Each complete A/B rational residue has zero tail at its own denominator order. Padding both finite local fractional sums to max K K1 therefore proves equality of their complete local truncations. The actual input, covector, all signed indices and the original homogeneous coefficient equation remain in scope. This compares local rational truncations; it does not by itself compare actual finite qFields."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ab-complete-pole-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue.ab_complete_pole_bound"),
                H("A binary Laurent numerator at the original pole bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For the same P,K and any I, G is a binary Laurent numerator divided by (y-z)^(L+M+(K-w-1).toNat). At w=r+j this is the required L+M+(K-r-j-1).toNat bound. Each local antidiagonal term has an additional pole of order at most K-w-1; multiplying by the stated power leaves a Laurent polynomial on the unchanged remaining labels. Finite numerator and fractional sums preserve this property. No replacement numerator or global caller-K locality premise is assumed.")),
                    Paragraph(Text("The faithful dependent source reconstructions in the Reg mirror compile, but the four-slot audits remain unfinished at issue #20163. Whole-family variation, sensitivity, observational dependence and the final sourceSelection/escapeFrom binding are not supplied; no declared_validated registration is claimed."))),
                DescribeRole.Theorem))));
}
