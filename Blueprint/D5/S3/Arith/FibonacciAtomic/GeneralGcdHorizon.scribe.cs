using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GeneralGcdHorizonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GeneralGcdHorizon.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power Fibonacci gcd horizons combine into an arbitrary-modulus consecutive-prefix theorem.",
        H("Arbitrary-Modulus Fibonacci Gcd Prefixes"),
        Blocks(
            Node("localHorizon", "Local prime-power threshold",
                "For e=1 this is the sharp prime horizon. For e>=2 it is the stagnant rank or the growth value (p-1) times the parent rank. The e=0 value is zero.",
                DescribeRole.Definition),
            Node("globalHorizon", "Global modulus threshold",
                "The threshold for H is the finite supremum of localHorizon(p,H.factorization p) over the prime divisors of H. It is zero for H=1.",
                DescribeRole.Definition),
            Node("gcd_value_consecutive_prefix", "Signed arbitrary-modulus prefix transport",
                "If a positive prefix reaches every local threshold of a positive modulus H, equality of signed gcd readings on that prefix determines equality at every positive time. The proof recombines the prime-power gcd components by unique factorization.",
                DescribeRole.Theorem),
            Node("actual_gcd_consecutive_prefix", "Natural-source prefix transport",
                "The same prefix condition determines all actual natural-source gcd futures, using the verified observation bridge from source coordinates to signed recurrence states.",
                DescribeRole.Theorem),
            Node("actual_gcd_global_prefix", "Finite supremum prefix theorem",
                "A prefix of length at least globalHorizon(H) determines every positive actual natural-source gcd reading for H. No initial quantity, primitive state, or residue-value observation is supplied for free.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("general-gcd-horizon-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement))), role);
}
