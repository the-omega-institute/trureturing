using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class RepresentativeOrbitCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Fourier coordinates at arbitrary doubling-orbit representatives form a linear equivalence into the actual generated fields.",
        H("Representative Fourier Coordinates over Finite Fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("representative-fourier-coordinates"),
                DeclarationHandle.Create("D5/S3/Fourier/RepresentativeOrbitCoordinates.representative_fourier_coordinates"),
                H("The actual orbit-field coordinate equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n be any odd integer at least three, d any integer at least one, "
                        + "F any finite field of characteristic two, and zeta a primitive nth root in F. "
                        + "Put G=(ZMod n)^(Fin d). Multiplication by two permutes G. Its full cycle "
                        + "quotient O includes the zero orbit and every other orbit. Choose any section "
                        + "sec:O->G of this quotient; the choice is unrestricted within each orbit.")),
                    Paragraph(Text(
                        "For t in G, K(t) is the intermediate field inside F generated over ZMod 2 "
                        + "by all zeta^(t(j).val), for j in Fin d. It is the actual adjoined subfield, "
                        + "with its inherited embedding into F. The theorem constructs a ZMod 2 linear "
                        + "equivalence from binary configurations a:G->ZMod 2 to the dependent product "
                        + "of K(sec(q)), q in O. After inclusion in F, its q coordinate is exactly "
                        + "sum_r algebraMap(a(r)) times product_j zeta^((sec(q)(j)*r(j)).val). "
                        + "Neither generation of F by zeta nor generation by occupied party labels is assumed.")),
                    Paragraph(Text(
                        "The character construction uses Mathlib AddChar.zmodChar and its primitive-root "
                        + "criterion; the scalar orthogonality input is AddChar.sum_mulShift. "
                        + "The orbit transport uses minimal periods of the actual doubling permutation, "
                        + "and its field extension step is IntermediateField.adjoin_induction. "
                        + "The resulting equivalence is a constructive finite-field Fourier consequence.")),
                    Paragraph(Text(
                        "Primitive additive-character orthogonality gives the inverse Fourier sum "
                        + "U(Y)(r)=sum_t Y(t) chi(-t,r). Odd n has value one in characteristic two, "
                        + "so there is no scalar normalization factor. A binary transform satisfies "
                        + "Y(2t)=Y(t)^2. Conversely, reindexing the inverse sum by the doubling permutation "
                        + "shows U(Y)(r)^2=U(Y)(r); each value is therefore zero or one and comes from "
                        + "the canonical ZMod 2 embedding. Both inverse identities use the same original "
                        + "product character chi(t,r).")),
                    Paragraph(Text(
                        "To realize arbitrary values in the actual fields, write k for the minimal "
                        + "period of sec(q). The kth Frobenius iterate fixes every generator of K(sec(q)). "
                        + "IntermediateField.adjoin_induction extends this equality through addition, "
                        + "multiplication, inversion and the prime field to every element of K(sec(q)). "
                        + "At an orbit position p^i(sec(q)), transport its prescribed value by i Frobenius "
                        + "iterates. Equality of two positions identifies their residues modulo k; "
                        + "the transported value is therefore independent of the chosen position. "
                        + "This constructs a compatible array for every dependent family of field values. "
                        + "The binary inverse realizes that entire array, proving surjectivity; "
                        + "representative transport and Fourier inversion prove injectivity. "
                        + "No dimension or independent-attainment premise is used.")),
                    Paragraph(Text(
                        "For qubit configurations, apply this scalar equivalence independently at each "
                        + "qubit index. The representative coordinates then range over the full products "
                        + "K(sec(q))^N. Empty parties impose no condition on these coordinates; N equal "
                        + "to zero gives the unique empty configuration. This coordinate result supplies "
                        + "no phase, trace, matrix rank, entropy or Gauss-sum evaluation. "
                        + "The finite-field Fourier argument is a classical consequence of character "
                        + "orthogonality and Frobenius transport; no literature novelty is asserted."))),
                DescribeRole.Theorem))));
}
