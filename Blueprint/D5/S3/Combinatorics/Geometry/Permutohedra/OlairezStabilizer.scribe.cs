using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class OlairezStabilizerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/olairez2026dihedralpermutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dihedral permutohedron has a full real affine symmetry for each permutation of paper labels and common sign.",
        H("The affine symmetry group in the original coordinates"),
        Blocks(
            Definition("affine-stabilizer", "affineStabilizer", "Intrinsic affine stabilizer",
                "For a set in a real affine space, take the subgroup of all real affine bijections whose image of that set is the set itself."),
            Definition("signs", "Signs", "The sign group",
                "Use the real units whose square is one, with multiplication."),
            Definition("sign-scalar", "signScalar", "Sign as a real number",
                "A sign acts by its underlying real number."),
            Definition("negative-sign", "negativeSign", "The negative sign",
                "Take minus one as an element of the sign group."),
            Definition("source-plane", "sourcePlane", "The intrinsic hyperplane",
                "For positive n, translate the real sum-zero direction through the constant vector with entry (n + 1) / 2."),
            Definition("source-center", "sourceCenter", "The intrinsic center",
                "For positive n regard the constant source center as a point of the intrinsic hyperplane."),
            Definition("source-hull", "sourceHull", "The hull in the intrinsic plane",
                "For positive n take the points of that hyperplane whose ambient vector belongs to the original dihedral orbit hull."),
            Definition("rotation", "sourceR", "Rotation with its paper label",
                "For positive n and a literal label from 1 through n, regard the corresponding rotation as a point of the intrinsic hyperplane."),
            Definition("antipode", "sourceF", "Antipode with its paper label",
                "For positive n and a literal label from 1 through n, regard the corresponding antipode as a point of the intrinsic hyperplane."),
            Definition("group-equivalence", "sourceStabilizerEquiv", "The group isomorphism",
                "For each natural n at least three, this multiplicative equivalence sends a permutation of the one-based paper labels and a common sign to the real affine preserver. The cyclic-difference chart conjugates the action to relabeling the wrap indices and multiplying by that sign."),
            Describe.Lean(
                DescribeId.Create("olairez-intrinsic-affine-symmetries"),
                DeclarationHandle.Create(Module + ".result"),
                H("Full real affine symmetry group"),
                StatementSource.FromAuthor(Disp(Seq(Forall, F.Id("n"), Geq, D(3), Colon, Quad,
                    Vert, Operatorname, Grp(F.Id("AffSym")), Open, Indexed("Q"), Close, Vert,
                    Eq, D(2), F.Id("n"), Bang))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural n at least three, the affine hull of the original orbit hull is exactly the real hyperplane with coordinate sum n(n + 1) / 2. The intrinsic vertices indexed by each paper label are the original rotation and antipode with that label.")),
                    Paragraph(Text("For every permutation σ of the labels 1 through n and every sign ε, the affine symmetry sends each rotation r_j to c + ε(r_{σ(j)} − c) and each antipode f_j to c + ε(f_{σ(j)} − c). The rotation formulas alone characterize a unique affine symmetry for each pair. Conversely, each affine preserver has a unique such pair.")),
                    Paragraph(Text("All preservers fix the center c. Composition is permutation composition and sign multiplication in the same order. The identity permutation with sign minus one is x ↦ 2c − x. The stabilizer has exactly 2n! elements.")),
                    Paragraph(Text("The wrap vectors span the sum-zero space, and their only dependence has all coefficients equal. Their signed hull has exactly those signed vertices and has centroid zero. An affine preserver fixes the centroid and permutes the antipodal pairs. The unique dependence forces a common sign across the pairs. The cyclic-difference equivalence carries this action back to the original labels. The result concerns the intrinsic real affine group of the standard-basepoint orbit. The lattice and arbitrary-basepoint questions have separate hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(string name) => Seq(F.Id(name), Underscore, Grp(F.Id("n")));

    private static DocumentBlock Definition(string id, string selector, string heading, string text) =>
        Describe.Lean(DescribeId.Create("olairez-stabilizer-" + id),
            DeclarationHandle.Create(Module + "." + selector), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
