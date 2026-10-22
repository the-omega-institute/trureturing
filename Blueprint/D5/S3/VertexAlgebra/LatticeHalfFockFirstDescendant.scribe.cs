using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFirstDescendantDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Charged First Descendant.",
        H("Actual Charged First Descendant"),
        Blocks(
            Paragraph(Text("The literal first source oscillator is evaluated through the existing finite Corr, correctedPolynomial and Ytw, not by defining a replacement descendant field. All colour sums are finite; the charge and lattice rank are unrestricted.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendant-corr-charged-first-oscillator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.Corr_charged_first_oscillator"),
                H("Charged first-oscillator correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every lattice, charge a and colour i, actual Corr of X(i,0) has exactly two coefficients: X(i,0) at shift zero and minus B(unit_i,a)/2 times the oscillator unit at shift one. The negative half is calculated from halfBinomial 1 in the existing insertion constructor. Corr_X_zero is not used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendant-charged-first-descendant-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.charged_first_descendant_field"),
                H("Actual field of the charged first oscillator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The proved charged Corr evaluation is consumed by correctedPolynomial and Ytw. The existing normalPolynomial_X and normalPolynomial_one identify the two constructor terms. A shift of one increases the charged cover exponent by two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendant-originalfirstdescendant-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_field"),
                H("Finite colour-linear descendant expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Ytw linearity expands the literal sum over colours of h(i) times Finsupp.single a X(i,0). This is a consumed organizational helper, not new mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendant-originalfirstdescendant-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_coefficient"),
                H("Coefficient of the literal descendant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The coefficient on every ActualTensor equals the finite colour sum of physical normal insertions minus B(h,a)/2 times the existing charged coefficient at E+2. This coefficient feeds the signed-cut bridge; no alternative carrier or assumed module law is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("These proofs are consumed by the signed-cut and original mixed-iterate modules. Kernel compilation is distinct from completed four-slot source admission. The Reg mirror contains typed obligations and a full dependent coefficient bridge; complete variation, sensitivity, observational dependence and structural source selection remain missing.")))));
}
