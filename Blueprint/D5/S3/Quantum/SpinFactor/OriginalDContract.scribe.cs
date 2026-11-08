using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinFactor;

internal sealed class OriginalDContractDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed positivity and finite phase balance on the original spin factor",
        H("Original-D positivity, unit rows, and finite label relations"),
        Blocks(
            Paragraph(Text("The complete original carrier is E = R x (Fin 3 -> R), with unit (1,0), Jordan product (s,x) o (t,y) = (st + x dot y, s y + t x), cone s >= sqrt(x dot x), and norm |s| + sqrt(x dot x). Evaluations retain every mass m >= sqrt(v dot v), including zero, unequal, and subnormalized masses.")),
            Paragraph(Text("The map D is an arbitrary total function on this same E. The results below derive their stated relations from the actual P2 and PB predicates. Additivity, homogeneity, continuity, unit rows, translation neutrality, three-label positivity, and the associator relation are not premises.")),
            Describe.Lean(
                DescribeId.Create("original-d-p2"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.P2"),
                H("Directed two-label positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every mass m and vector v with m >= sqrt(v dot v), and every two original elements a,b, the directed complex matrix with entries alpha(a_i o a_j) - i alpha(D(a_i,a_j)) is positive semidefinite. Both directed off-diagonal entries come from the same total D."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-d-pb"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.PB"),
                H("Original plus and minus phase balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive evaluation and every original triple a,b,c, the square readouts at r = b + D(a,b) - a o c, s = c + a o b + D(a,c), and at the corresponding opposite signs, agree. Every inner and outer occurrence uses the same original D."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-d-skew"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.p2_skew"),
                H("The original directed relation is antisymmetric"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D satisfying P2 and all original a,b, D(b,a) = -D(a,b). Hermitian symmetry of the actual two-label table gives the equality in every positive readout; scalar and coordinate evaluations separate original elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-determinant"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.p2_determinant_bound"),
                H("The real off-diagonal entry remains in the determinant bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D satisfying P2, every positive evaluation alpha, and all a,b, alpha(D(a,b)) squared is at most alpha(a squared) alpha(b squared) minus alpha(a o b) squared. This includes zero mass and all degenerate labels. The known real Jordan term is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-proportional"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.p2_proportional"),
                H("All real proportional inputs have zero output"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D satisfying P2, every real r and every original a, both D(r a,a) and D(a,r a) are zero. The known Jordan determinant is zero on such a pair; the separating positive evaluations give the element equality, including r = 0 and negative r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.p2_zero_rows"),
                H("Both original zero rows vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D satisfying P2, D(0,b) = 0 and D(a,0) = 0 for every original a,b. These equalities are used in the degenerate unit-row cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-difference"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.pb_iff_finite_difference"),
                H("Phase balance is the element-valued finite-difference law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D, PB is equivalent to finiteDifference(D,a,b,c) = 0 for all original triples. Writing d = D(a,b) - a o c and e = a o b + D(a,c), this is D(b+d,c+e) - D(b-d,c-e) = -2 b o d - 2 c o e. Expanding only the known Jordan squares makes the readout difference twice the evaluation of this residual. No input sum is expanded through D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-nonzero-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.unit_row_nonzero_scalar"),
                H("Nonzero scalar labels eliminate the unit row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D satisfying P2 and PB, all real l,t and every vector y with t nonzero, D((l,0),(t,y)) = 0. P2 first puts the output on the scalar zero face, perpendicular to y. If z is its vector part and Z its length, take the actual evaluation (Z,z) and the finite scalar k = l Z / (1+l squared). Both outer Jordan determinants vanish. The element-valued balance then forces t Z squared = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-unit"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.unit_rows"),
                H("All original unit rows vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every total D satisfying P2 and PB, every real q and every original b, D((q,0),b) = 0. This includes pure-vector b, q = 0, and zero vectors. The pure-vector case uses proportional inner labels and equal b,c to obtain a zero outer pair; a finite Cayley label substitution with parameter sqrt(2)-1 connects it to the desired scalar/vector pair. Its two inner scalar parts are nonzero, so the preceding unit-row result applies. No limit or homogeneity of D is used."))),
                DescribeRole.Theorem)))));
}
