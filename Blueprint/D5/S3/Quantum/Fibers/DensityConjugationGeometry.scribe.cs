using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class DensityConjugationGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Fibers/DensityConjugationGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal conjugation quotient of all nonreal normalized five-mode density "
            + "matrices has real Hausdorff dimension twenty-four in its finite orbit metric.",
        H("Geometry of the Actual Density Conjugation Quotient"),
        Blocks(
            Definition("coordinates", "Coordinates", "Centered Hermitian coordinates",
                "The real coordinate space consists of trace-zero Hermitian five-by-five "
                    + "complex matrices. It carries the entrywise supremum norm inherited from "
                    + "matrices, namely the maximum complex absolute value of an entry."),
            Definition("coordinate", "coordinate", "Coordinates of a physical density matrix",
                "Subtract one fifth of the identity from the native positive trace-one density "
                    + "matrix. Reconstruction adds that same matrix. The coordinate map is "
                    + "injective, and every physical coordinate reconstructs a positive trace-one state."),
            Definition("physical", "physical", "The actual positivity domain",
                "A centered coordinate is physical exactly when adding one fifth of the "
                    + "identity gives a positive semidefinite matrix. Trace one follows from "
                    + "the trace-zero coordinate condition. No determinant, purity, or rank "
                    + "condition restricts this set."),
            Definition("transpose", "transpose", "Conjugation as an isometric involution",
                "Transposition preserves the centered Hermitian space and its norm. On a "
                    + "Hermitian matrix it is entrywise complex conjugation. Subtraction of "
                    + "the real center commutes with conjugation."),
            Definition("realization", "orbitRealization", "An explicit realization of the literal quotient",
                "The input is the literal quotient of native density states by equality or "
                    + "conjugation. Centered coordinates map it injectively into the orbit "
                    + "space of transposition. The metric on the density quotient is induced "
                    + "by this map, so the map is an isometry onto its image. The distance is "
                    + "the smaller of the two matrix distances obtained by conjugating either "
                    + "representative. This is a nonlinear finite orbit quotient."),
            Definition("nonreal", "fiveModeNonrealQuotient", "The entire nonreal quotient subset",
                "This is the image of every native density state that differs from its "
                    + "conjugate. All nonreal singular states are included. Real density states "
                    + "remain in the ambient quotient as its fixed stratum."),
            Describe.Lean(DescribeId.Create("dimension"),
                DeclarationHandle.Create(Module + "five_mode_nonreal_quotient_dimension"),
                H("Intrinsic real Hausdorff dimension twenty-four"),
                StatementSource.FromAuthor(Disp(Seq(C("dimH", C("fiveModeNonrealQuotient")),
                    Eq, D(2, 4)))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Actual positive and negative density perturbations span every "
                        + "trace-zero Hermitian direction. Convexity then proves that the physical "
                        + "coordinate domain has nonempty interior. The fixed subspace is proper, "
                        + "as witnessed by the existing physical conjugate pair. Removing that "
                        + "subspace leaves a set with nonempty interior and Hausdorff dimension "
                        + "twenty-four. These steps construct the dimensional correspondence.")),
                    Paragraph(Text("The finite isometric involution theorem preserves the "
                        + "Hausdorff dimension of this entire set. The explicit quotient "
                        + "realization transfers the result to the literal density quotient. "
                        + "This does not assert a smooth manifold chart at singular density states.")),
                    Paragraph(Text("Complete real statistics on every fixed number of independent "
                        + "copies at least two have precisely these orbit fibers by "
                        + "real_copy_classification. A nonreal orbit has the two distinct states "
                        + "rho and its conjugate; conjugation preserves matrix rank. The real "
                        + "locus is fixed. The normalized one-copy statistical image has affine "
                        + "dimension fourteen by five_mode_physical_image_dimension. The supplied "
                        + "states pairState one and pairState minus one are distinct positive "
                        + "trace-one conjugate states and furnish a concrete candidate pair."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula C(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
