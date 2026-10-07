using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeSugawaraVirasoroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeSugawaraVirasoro.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quadratic modes satisfy all-integer Virasoro with central charge equal to lattice rank.",
        H("Actual All-Charge Sugawara Virasoro Law"),
        Blocks(
            Paragraph(Text("Assume precisely H Gc=Gc H=1 on the complex Gram matrix of the existing even "
                + "lattice. The current commutator implies that the Virasoro defect commutes with "
                + "all currents. Restricting to each charge sector, inverse-Gram differentiation "
                + "and polynomial induction make the commutant scalar. This directly uses the "
                + "frozen private eq_constant_of_partials_zero of ConditionalPolynomialRigidity. "
                + "Weighted Euler kills the off-diagonal defect; diagonal evaluation retains and "
                + "cancels the charged boundaries before computing the inverse-Gram trace and "
                + "cubic oscillator sum.")),
            Describe.Lean(
                DescribeId.Create("actual-lattice-virasoro"),
                DeclarationHandle.Create(Prefix + "sugawaraMode_virasoro"),
                H("All-integer Virasoro with central charge equal to rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every pair of integers m,n, the actual "
                        + "endomorphisms satisfy [L(m),L(n)]=(m-n)L(m+n) plus "
                        + "rank(D)(m^3-m)/12 times delta(m+n,0) id. The current law "
                        + "gives [L(m),h_i(q)]=-q h_i(m+q). The central defect commutes "
                        + "with all currents and is scalar independently on each "
                        + "charge sector. Weighted Euler kills the off-diagonal defect.")),
                    Paragraph(Text("For a>0, evaluating L(a)L(-a) on single(beta,1) "
                        + "keeps both charged boundary terms. Subtracting 2a L(0) "
                        + "cancels their charge contribution. The remaining inverse-Gram "
                        + "trace is rank(D), and the oscillator sum is (a^3-a)/6. "
                        + "Skew symmetry supplies negative diagonal modes and the "
                        + "zero diagonal is zero. Consequently the scalar is the "
                        + "same on every integral charge sector."))),
                DescribeRole.Theorem),
            Paragraph(Text("The charge-sensitive lattice conformal construction is classical: Bakalov-Kac, "
                + "arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16). The finite "
                + "commutator organization is adapted from Kytola at revision "
                + "5ff4245383b2cdd4eea7a0524bc1274c32041eb4. No positivity or fixed-charge Fock "
                + "transfer is assumed.")))));
}
