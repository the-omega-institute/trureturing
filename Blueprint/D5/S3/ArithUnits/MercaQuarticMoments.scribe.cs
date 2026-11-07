using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaQuarticMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaQuarticMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    private static readonly LibraryNoteRef AnalyticSource =
        LibraryNoteRef.Create("D5/L/ArithUnits/yaoxu2026catalanmoment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized quartic character's actual first Bernoulli value has odd nonzero "
            + "integer coordinates, obtained from the least-positive representative sums "
            + "in its ordered kernel cosets. Its analytic L-value at zero is the negative "
            + "of this same finite sum.",
        H("Actual Quartic Character Moments"),
        Blocks(
            Paragraph(Text("Throughout, r is prime, r mod 8 is 5, chi is the unique "
                + "character with order four and chi(2)=i, K is its actual unit kernel, "
                + "and m=(r-1)/4. All representatives are ZMod.val. Every unit has "
                + "representative strictly between zero and r, so these are precisely "
                + "the source's least-positive representatives. The coordinate theorem "
                + "and divisibility require r>5. This excludes the singleton kernel at r=5.")),
            Node("two", "The unit two", "twoUnit", DescribeRole.Definition,
                "The native unit represented by two modulo r. No assumption about its order is made."),
            Node("sum", "Coset representative sum", "sumRep", DescribeRole.Definition,
                "For every native unit c, sumRep r c is the integer sum of val(u) over "
                    + "the finite set of native units u with c inverse times u in K. "
                    + "It is the literal least-positive representative sum s(cK)."),
            Node("coordinate", "The integral coset coordinate", "coordinate", DescribeRole.Definition,
                "The integer expression 2 times the integer quotient s(cK)/r minus m. "
                    + "Divisibility in the following theorem proves the quotient is exact "
                    + "on the r>5 domain; it is not an assumed class number."),
            Node("real", "Real coordinate", "realCoordinate", DescribeRole.Definition,
                "The coordinate k of the identity coset K, in the orientation chi(2)=i."),
            Node("imaginary", "Imaginary coordinate", "imagCoordinate", DescribeRole.Definition,
                "The coordinate t of the actual coset 2K, in the orientation chi(2)=i."),
            Node("bernoulli", "The actual first Bernoulli value", "bernoulli", DescribeRole.Definition,
                "B is the complex sum of val(u) times chi(u) over all native units modulo "
                    + "r, divided by r. Nonunits have character value zero, so this is "
                    + "also the full residue-class sum divided by r."),
            Node("representatives", "Divisibility, complementation and oddness",
                "representative_properties", DescribeRole.Theorem,
                "For every prime r>5 with r mod 8 equal to 5, all unit representatives "
                    + "are positive and below r. For every coset cK, r divides s(cK), "
                    + "s(-cK)=r m-s(cK), and its integral coordinate is odd and nonzero. "
                    + "The kernel has m>1 elements. Multiplication by a nonidentity kernel "
                    + "element permutes every coset and fixes its residue-class sum. "
                    + "In the prime field that forces the sum to zero. Negation permutes "
                    + "cK onto -cK and replaces each representative a by r-a. "
                    + "Finally m is odd, so twice an integer minus m is odd."),
            Node("coordinates", "The actual Bernoulli coordinates and L-value",
                "bernoulli_coordinates", DescribeRole.Theorem,
                "For every prime r>5 with r mod 8 equal to 5, let k and t be the "
                    + "preceding integer coordinates. Then B=k+i t; k and t are odd "
                    + "and nonzero; k=2s(K)/r-m and t=2s(2K)/r-m in the rationals; "
                    + "B is the literal sum of a chi(a) for a=1,...,r-1 divided by r; "
                    + "and the actual Dirichlet L-function satisfies L(0,chi)=-B. "
                    + "The character fibers are the ordered cosets K, 2K, -K, -2K "
                    + "with values 1, i, -1, -i. Decompose the moment along these "
                    + "fibers and use the complement identities and exact divisibility. "
                    + "For the final analytic equality, apply the existing prime nonprincipal "
                    + "character special-value theorem with its hypotheses discharged.",
                AssessedProvenance.FromLiterature(Source, AnalyticSource))),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/MercaQuarticCharacter")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/MercaPrimeCharacterMoment"))]));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("merca-quartic-moments-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
