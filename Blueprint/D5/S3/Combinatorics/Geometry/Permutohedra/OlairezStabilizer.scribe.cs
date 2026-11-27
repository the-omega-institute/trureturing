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
                StatementSource.FromAuthor(StabilizerFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The ambient coordinate space Vₙ is indexed by residues Zₙ, and Pₙ is the intrinsic source plane with inclusion ι into Vₙ. The hull Qₙ is in Vₙ, and Hₙ is its preimage in Pₙ. Write Aₙ for the group of real affine bijections of Pₙ that carry Hₙ onto itself. The ambient center is c and its point in Pₙ is C.")),
                    Paragraph(Text("Lₙ consists of the literal paper labels 1 through n. The bar on a label denotes its residue, so label n has residue zero. Rₐ and Fₐ are the intrinsic vertices, and r and f are the original residue-indexed families. The affine map φ for each permutation and sign is the image of that pair under the group equivalence above. The signs in the ambient action formulas act by their real scalars.")),
                    Paragraph(Text("The wrap vectors span the sum-zero space, and their only dependence has all coefficients equal. Their signed hull has exactly those signed vertices and has centroid zero. An affine preserver fixes the centroid and permutes the antipodal pairs. The unique dependence forces a common sign across the pairs. The cyclic-difference equivalence carries this action back to the original labels. The result concerns the intrinsic real affine group of the standard-basepoint orbit. The lattice and arbitrary-basepoint questions have separate hypotheses."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("olairez-2026-dihedral-permutohedron-affine-symmetries"),
                    ResolutionKind.Proved)))));

    private static Formula StabilizerFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), x = F.Id("x"), a = F.Id("a");
        Formula t = F.Id("T"), center = F.Id("c"), intrinsicCenter = F.Id("C");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula residues = Indexed(Seq(Mathbb, Grp(F.Id("Z"))), n);
        Formula coordinates = Indexed(F.Id("V"), n), plane = Indexed(F.Id("P"), n);
        Formula hull = Indexed(F.Id("Q"), n), labels = Indexed(F.Id("L"), n);
        Formula stabilizer = Indexed(F.Id("A"), n);
        Formula pairs = Seq(Call(Op("Sym"), labels), Sp, Times, Sp,
            OpenBrace, D(1), Comma, Sp, Minus, D(1), CloseBrace);
        Formula pair = Pair(SigmaLower, Varepsilon);
        Formula secondPair = Pair(Tau, Alpha);
        Formula composedPair = Pair(Seq(SigmaLower, Sp, Circ, Sp, Tau), Seq(Varepsilon, Alpha));
        Formula rotation = Indexed(F.Id("R"), a), antipode = Indexed(F.Id("F"), a);
        Formula residue = Seq(Overline, Grp(a));
        Formula apply(Formula parameters, Formula point) => Call(Indexed(Phi, parameters), point);
        Formula signedVertex(string family) => Seq(center, Plus, Varepsilon, Sp, Cdot, Sp, Open,
            Call(Iota, Indexed(F.Id(family), Call(SigmaLower, a))), Minus, center, Close);
        Formula rotationLaw = Seq(All(a, labels), Call(Iota, Call(t, rotation)), Eq, signedVertex("R"));

        return Disp(new Formula.Aligned([
            Seq(Amp, All(n, Seq(Mathbb, Grp(F.Id("N")))), n, Geq, D(3), Sp, Implies),
            Seq(Amp, Open, Call(Indexed(Op("aff"), reals), hull), Eq, plane),
            Seq(Amp, Land, Sp, Open, All(x, coordinates), In(x, plane), Sp, Iff, Sp,
                Sum, Underscore, Grp(In(i, residues)), Indexed(x, i), Eq,
                new Formula.Fraction(Seq(n, Open, n, Plus, D(1), Close), D(2)), Close),
            Seq(Amp, Land, Sp, Open, All(a, labels), Call(Iota, rotation), Eq,
                Indexed(F.Id("r"), residue), Sp, Land, Sp, Call(Iota, antipode), Eq,
                Indexed(F.Id("f"), residue), Close),
            Seq(Amp, Land, Sp, Open, All(pair, pairs), All(a, labels),
                Call(Iota, apply(pair, rotation)), Eq, signedVertex("R")),
            Seq(Amp, Quad, Land, Sp, Call(Iota, apply(pair, antipode)), Eq,
                signedVertex("F"), Close),
            Seq(Amp, Land, Sp, Open, All(pair, pairs), Exists, Bang, Sp,
                In(t, stabilizer), Comma, Sp, rotationLaw, Close),
            Seq(Amp, Land, Sp, Open, All(t, stabilizer), Exists, Bang, Sp,
                In(pair, pairs), Comma, Sp, rotationLaw, Close),
            Seq(Amp, Land, Sp, Open, All(t, stabilizer), Call(t, intrinsicCenter), Eq,
                intrinsicCenter, Close),
            Seq(Amp, Land, Sp, Open, All(Seq(pair, Comma, secondPair), pairs), All(x, plane),
                apply(composedPair, x), Eq, apply(pair, apply(secondPair, x)), Close),
            Seq(Amp, Land, Sp, Open, All(x, plane),
                Call(Iota, apply(Pair(D(1), Seq(Minus, D(1))), x)), Eq,
                D(2), Sp, Cdot, Sp, center, Minus, Call(Iota, x), Close),
            Seq(Amp, Land, Sp, Call(Op("card"), stabilizer), Eq, D(2), Sp, Cdot, Sp, n, Bang, Close),
        ]));
    }

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Indexed(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Call(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pair(Formula first, Formula second) => Seq(Open, first, Comma, second, Close);
    private static Formula In(Formula value, Formula domain) => Seq(value, Sp, InMacro, Sp, domain);
    private static Formula All(Formula variables, Formula domain) =>
        Seq(Forall, Sp, In(variables, domain), Comma, Sp);

    private static DocumentBlock Definition(string id, string selector, string heading, string text) =>
        Describe.Lean(DescribeId.Create("olairez-stabilizer-" + id),
            DeclarationHandle.Create(Module + "." + selector), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
