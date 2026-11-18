using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSigned;

internal sealed class JLTConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/johnstonleongtudzi2026summatory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The large-parameter limit of the signed Omega summatory limsup.",
        H("Johnston-Leong-Tudzi Conjecture 5.1"),
        Blocks(
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"),
                H("The signed summatory function"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For real a and x, W(a,x) is the sum of "
                    + "(-a)^Omega(n) over natural n in the closed interval from one "
                    + "to the natural floor of x. Omega is ArithmeticFunction.cardFactors: "
                    + "it counts prime factors with multiplicity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("s"),
                DeclarationHandle.Create(Prefix + "s"),
                H("The normalized limsup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For real a, s(a) is the real filter limsup at "
                    + "positive infinity of |W(a,x)|/x^(logb(2,a)), with x real. "
                    + "The source uses a>2. The estimates here provide the boundedness "
                    + "needed for the real limsup when a>=64."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("b"),
                DeclarationHandle.Create(Prefix + "B"),
                H("The error bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real a, B(a) is "
                    + "(1/2)*3^(2-logb(2,a)/3). It tends to zero as a tends to "
                    + "positive infinity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitative"),
                DeclarationHandle.Create(Prefix + "quantitative"),
                H("Two-sided quantitative bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real a>=64, "
                    + "a/(a+1)-B(a)<=s(a) and s(a)<=1+B(a). Every positive integer "
                    + "has a unique representation 2^j*m with m odd. The geometric "
                    + "sum on each such fiber has absolute value at most a^J. "
                    + "The existing odd_part_lower theorem of PrimeExponentRecordLimitOne, "
                    + "via cardFactors_apply, gives 3^Omega(m)<=m for odd m. "
                    + "Consequently 2^(3*Omega(m))<=m^2. "
                    + "With v=logb(2,a)>=6, the normalized odd weight is at most "
                    + "m^(-v/3). Its tail from three is bounded by "
                    + "3^(2-v/3) times the telescoping sum of 1/(m*(m-1)), "
                    + "hence by B(a). The odd part one supplies the main geometric "
                    + "sum. The upper estimate holds for every real x>=1, and the "
                    + "lower estimate follows along x=2^k. Eventual upper boundedness "
                    + "and lower coboundedness justify both limsup comparisons."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjectured limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The function s tends to one as the real "
                    + "parameter a tends to positive infinity. The proof applies "
                    + "quantitative: its lower endpoint tends to one because "
                    + "a/(a+1) tends to one and B(a) tends to zero; its upper endpoint "
                    + "also tends to one. The squeeze theorem gives the claimed "
                    + "limit. This establishes precisely Conjecture 5.1, and gives "
                    + "no eventual strict bound from Conjecture 1.4, even for large fixed a, "
                    + "and no conclusion about Sun's conjecture at a=2."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("johnston-leong-tudzi-2026-conjecture-5-1"),
                    ResolutionKind.Proved)))));
}
