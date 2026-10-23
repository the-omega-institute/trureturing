using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class SignedBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/SignedBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every length, the signed boundary of the actual legal-word graph has mass-zero "
        + "image and gives the natural short exact sequence for singleton occupation.",
        H("Signed boundaries of legal-word toggle graphs"),
        Blocks(
            Paragraph(Text(
                "Legal n consists of the existing Boolean words on Fin n satisfying Adm. "
                + "The value at position j represents membership of j+1 in the independent "
                + "support in positions 1 through n. legalWordGraph n is the existing induced "
                + "hypercube: adjacency means exactly one differing coordinate. The edge "
                + "space has one real coordinate for each actual unordered edge, and the "
                + "vertex space has one real coordinate for each actual legal word.")),
            Paragraph(Text(
                "Orientation G chooses an ordered pair of endpoints for each member of "
                + "G.edgeSet, whose unordered pair is that same edge. No edge is doubled. "
                + "edgeVector is the real cast of the existing signedIncidence column: "
                + "the delta at the head minus the delta at the tail. vertexDelta v is "
                + "Pi.single v 1. signedBoundary o sends a real edge coefficient function "
                + "f to the sum of f e times edgeVector o e. Coefficients may have either sign; "
                + "reference orientation places no restriction on an executable direction.")),
            Paragraph(Text(
                "totalMass sums all vertex coordinates, and totalMassZero is its linear "
                + "kernel. observation n sends a vertex function v to the coordinate "
                + "whose value at i is the sum of v b over all actual words with b.val i=true. "
                + "This is precisely singleton occupation of that same support carrier.")),
            Paragraph(Text(
                "kernelBoundaryInclusion A o is the linear map from ker B to ker(A B) "
                + "sending f to the identical edge function f. restrictedBoundary A o "
                + "sends f in ker(A B) to B f in ker(A restricted to totalMassZero), retaining "
                + "the mass-zero and observation-zero certificates. These definitions "
                + "specify the maps in the sequence, rather than only asserting the "
                + "existence of some isomorphic spaces.")),
            Describe.Lean(DescribeId.Create("native-boundary-image-short-exact"),
                DeclarationHandle.Create(Prefix + "native_boundary_image_short_exact"),
                H("The image and the natural short exact sequence"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n and every reference orientation o of "
                        + "legalWordGraph n, the image of signedBoundary o is totalMassZero. "
                        + "The stated kernel inclusion is injective, its image is the kernel "
                        + "of restrictedBoundary, and restrictedBoundary is surjective. "
                        + "Thus the zero spaces at the two ends complete a short exact "
                        + "sequence of real vector spaces. No connectivity, rank or image "
                        + "equality is assumed.")),
                    Paragraph(Text(
                        "Delete an occupied coordinate using the existing legal-word "
                        + "deletion operation. Its existing adjacency and occupation "
                        + "identities show that this is an actual graph step and that "
                        + "occupation decreases by one. Strong induction therefore gives "
                        + "a path from every legal word to the empty word, proving connectivity "
                        + "of the native graph at every length.")),
                    Paragraph(Text(
                        "For an adjacent pair, the chosen orientation agrees with the "
                        + "path direction or reverses it. Assigning coefficient 1 or -1 "
                        + "to that one unordered edge gives the desired endpoint delta "
                        + "difference. Induction on a walk telescopes these differences. "
                        + "Every mass-zero function x is the sum, over all vertices v, of "
                        + "x v times the delta at v minus the delta at a fixed root. Each "
                        + "difference is a boundary, and every boundary has mass zero; "
                        + "these two inclusions prove the image equality.")),
                    Paragraph(Text(
                        "If a mass-zero vertex function has zero observation, lift it "
                        + "through the image equality to an edge function f. Then A B f=0, "
                        + "so the lift lies in the middle kernel. The restricted map has "
                        + "kernel exactly ker B, giving exactness. At n=0 there is one "
                        + "legal vertex and no edge; both the image and mass-zero space "
                        + "are zero and the same statement applies. This does not assert "
                        + "that A B vanishes on the whole edge space. Dimension and numerical "
                        + "count formulas are separate claims."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), o = F.Id("o");
        Formula a = Call("observation", n);
        Formula inclusion = Call("kernelBoundaryInclusion", a, o);
        Formula restriction = Call("restrictedBoundary", a, o);
        return Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))),
            All("o", Call("Orientation", Call("legalWordGraph", n)),
                And(Eq(Call("range", Call("signedBoundary", o)),
                    Call("totalMassZero", Call("Legal", n))),
                    And(Call("Injective", inclusion),
                        And(Call("Exact", inclusion, restriction), Call("Surjective", restriction)))))));
    }
}
