using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedMonodromyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate monodromy of actual native charged coefficients", H("Actual Cover Monodromy"), Blocks(
            Paragraph(Text("D has arbitrary finite rank, integral symmetric even-diagonal Gram matrix; hu:IsUnit D.G.det. "
                + "Charges a are unrestricted and e ranges over all integers. States lie in the full native oscillator "
                + "polynomial algebra tensor the actual quotient ground module selected from "
                + "actual_twisted_ground_representation D hu. There is no occupation cutoff or positivity assumption.")),
            Describe.Lean(DescribeId.Create("actual-coordinate-monodromy"),
                DeclarationHandle.Create(Prefix + "charged_coefficient_coordinate_monodromy"), H("Native coefficient identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly chargedCoefficient D hu (-a) e=(-1)^e smul chargedCoefficient D hu a e, "
                    + "as endomorphisms of ActualTensor D hu. The odd logarithm changes sign under x -> -x; "
                    + "native creation coefficients acquire (-1)^degree, and finite translation coefficients acquire "
                    + "the same odd-frequency substitution sign. The norm q_a is even and q_(-a)=q_a, "
                    + "so the product of term signs is (-1)^e and the scalar 2^(-q_a) is unchanged.")),
                    Paragraph(Text("Native K_eq_kernel and mod-two reduction identify the quotient lifts of -a and a, "
                        + "hence U_(-a)=U_a. No replacement of U_(-a) by U_a inverse is made: the square of U_a "
                        + "retains the half-norm sign of the actual representation. This is coordinate monodromy "
                        + "for z=x^2, not an all-state twisted Jacobi or reconstruction theorem. Classical provenance, "
                        + "zero novelty claim. Full moonshine, orbifold, fusion, string and AdS/CFT realization remain open."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-ground-reflection"),
                DeclarationHandle.Create(Prefix + "ground_neg"), H("Ground reflection in the actual quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The actual ground-action endomorphisms for a and -a are equal because their mod-two quotient lifts agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-norm-reflection"),
                DeclarationHandle.Create(Prefix + "norm_neg"), H("Norm reflection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The integral lattice norm is unchanged under charge negation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-norm-even"),
                DeclarationHandle.Create(Prefix + "norm_even"), H("Even lattice norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every integral charge has even norm for the given symmetric even-diagonal Gram matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-creation-reflection"),
                DeclarationHandle.Create(Prefix + "creation_neg"), H("Creation coefficient reflection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every signed creation degree e, charge negation multiplies its oscillator coefficient by (-1)^e. Negative degrees remain zero. These identities give the exact coordinate characters used in the reflected charged residue kernels."))), DescribeRole.Theorem))));
}
