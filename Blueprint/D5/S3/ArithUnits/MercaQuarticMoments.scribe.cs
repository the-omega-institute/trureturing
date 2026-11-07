using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaQuarticMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaQuarticMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized quartic character's actual first Bernoulli value has odd nonzero "
            + "integer coordinates, obtained from the least-positive representative sums "
            + "in its ordered kernel cosets. Its analytic L-value at zero is the negative "
            + "of this same finite sum. The actual CRT kernel has the full coordinate "
            + "criterion for centered first moments, including conjugation.",
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
                AssessedProvenance.FromLiterature(Source)),
            Node("lifted-kernel", "The actual lifted kernel", "liftedKernel", DescribeRole.Definition,
                "H is the reduction preimage of K in the native units modulo r q."),
            Node("crt", "The actual CRT identification", "liftedKernelEquiv", DescribeRole.Definition,
                "For coprime r and q, the native Chinese remainder equivalence restricts "
                    + "to a multiplicative equivalence from H to K times the full unit group "
                    + "modulo q. Its first coordinate is reduction modulo r."),
            Node("structure", "Cyclicity, index and the omitted involution", "lifted_structure",
                DescribeRole.Theorem,
                "For distinct primes q and r with r congruent to five modulo eight, "
                    + "H is cyclic exactly when gcd(m,q-1)=1, has index four, and omits "
                    + "minus one. Both CRT factors are cyclic, with orders m and q-1. "
                    + "The finite product cyclicity theorem gives the exact criterion. "
                    + "Surjectivity of reduction preserves the kernel index, and minus "
                    + "one reduces to the already excluded local involution."),
            Node("center", "The literal centered sum", "centered", DescribeRole.Definition,
                "The integer identity twice the sum of the least-positive representatives "
                    + "of H equals r q m(q-1). Only H itself is tested."),
            Node("centered-coordinates", "The full prime-lift coordinate criterion",
                "centered_coordinates", DescribeRole.Theorem,
                "For every prime r>5 congruent to five modulo eight and every distinct "
                    + "prime q, H has order m(q-1), all its native unit representatives "
                    + "are strictly between zero and r q, and its literal sum is centered "
                    + "if and only if chi(q)=1, or k=t and chi(q)=-i, or k=-t and "
                    + "chi(q)=i. The existing coset-fiber lift gives deviation equal to "
                    + "q times s(K)-s(q inverse K). The four values of chi(q) identify "
                    + "the inverse coset. The complement identities give the three "
                    + "branches and k nonzero excludes chi(q)=-1. This finite first-moment "
                    + "identity needs neither q>3 nor q>r; it applies in particular to "
                    + "every admissible odd prime in the MMZ domain. The subsequent "
                    + "class-number and sign bridges remain separate proof obligations.",
                AssessedProvenance.FromLiterature(Source)),
            Node("generator", "The eligible source generators", "generator_eligible",
                DescribeRole.Theorem,
                "For r>5 and distinct odd prime q, every generator of H has representative "
                    + "a with gcd(a-1,r q)=1. Its projections generate both local factors. "
                    + "Both factors have order greater than one, so neither projection "
                    + "is the identity. Reduction shows a-1 is a unit at both primes. "
                    + "Together with lifted_structure this retains exactly the source "
                    + "generator eligibility on gcd(m,q-1)=1."),
            Node("conjugation", "Conjugation and the branch orientation", "conjugate_coordinates",
                DescribeRole.Theorem,
                "The conjugate character has order four, value -i at two, the identical "
                    + "native kernel, value -1 at minus one and value i on -2K. Its "
                    + "actual Bernoulli sum is k+i(-t). Thus the same ordered cosets "
                    + "K,2K,-K,-2K now have values 1,-i,-1,i. The centered branch k=t "
                    + "uses the conjugate q-value i, and k=-t uses -i. This is an "
                    + "explicit simultaneous transformation of character values and "
                    + "imaginary coordinate; the normalized sign formula is not reused "
                    + "unchanged.")),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/MercaQuarticCharacter")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/MercaPrimeCharacterMoment")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/MercaCosetFiberLift"))]));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("merca-quartic-moments-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
