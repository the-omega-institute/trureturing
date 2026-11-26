using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class StrongPseudoperfectEulerDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mccormackzelinsky2023weightedamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong pseudoperfection is a strong restriction on Euler-form integers.",
        H("McCormack and Zelinsky's Question 44"),
        Blocks(
            Describe.Lean(DescribeId.Create("euler-form"),
                DeclarationHandle.Create(Prefix + "EulerForm"),
                H("Euler forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An Euler-form integer has a representation q^s*m^2 "
                    + "with q prime, q and s congruent to one modulo four, m positive, and "
                    + "q coprime to m. No oddness condition is imposed on m. The allowed "
                    + "exponents include 1, 5, 9, and every further positive exponent "
                    + "congruent to one modulo four."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("euler-count"),
                DeclarationHandle.Create(Prefix + "eulerCount"),
                H("Counting Euler forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The count is over integers from 1 to X, "
                    + "so different Euler representations of one integer are counted once."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("euler-sp-count"),
                DeclarationHandle.Create(Prefix + "eulerSPCount"),
                H("Counting strongly pseudoperfect Euler forms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The count uses the existing complementary-divisor "
                    + "definition of strongly pseudoperfect positive integers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A strong restriction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The quotient eulerSPCount(X)/eulerCount(X) tends "
                        + "to zero. Thus being strongly pseudoperfect is a strong restriction "
                        + "on the Euler set, answering Question 44. This is a relative "
                        + "density statement; Question 43 concerns density among all integers.")),
                    Paragraph(Text("For the exponent-one part q*m^2, the existing prime "
                        + "subset code gives q as a quotient with numerator a divisor subset "
                        + "sum of m^2. Hence q is at most sigma(m^2). Every positive divisor "
                        + "d has a decomposition b^2*a with a squarefree. The implication "
                        + "a*b^2 divides m^2 if and only if a*b divides m requires no "
                        + "coprimality between a and b. Selecting one such decomposition "
                        + "for each divisor injects into the finite set of positive pairs "
                        + "with a*b dividing m.")),
                    Paragraph(Text("Interchanging finite sums and counting positive "
                        + "multiples gives a bound by the sum over a of T*(floor(T/a))^2. "
                        + "The inverse-square estimate makes this at most 2*T^3, and "
                        + "therefore at most 3*T^3. With T the integer part of X^(1/4), "
                        + "small square factors contribute at most 3*X^(3/4). Large square "
                        + "factors contribute at most 2*X/(T+1), at most 2*X^(3/4).")),
                    Paragraph(Text("Every allowed exponent at least five is 5+4*j; absorbing "
                        + "q^(2*j) into m writes the integer as q^5*a^2. It follows that "
                        + "a*q^2 is at most the integer square root of X. Summing the "
                        + "resulting floor bounds over q at least two contributes at most "
                        + "sqrt(X). These are upper bounds on images of parameter sets, "
                        + "so repeated representations do not require uniqueness.")),
                    Paragraph(Text("Consequently eulerSPCount(X) is at most 6*X^(3/4) "
                        + "for X at least sixteen. Every prime congruent to one modulo four "
                        + "is an Euler form with s=m=1. The classical Dirichlet--Mertens "
                        + "estimate used here gives at least exp(-50)*X/log(X) such primes "
                        + "for X at least exp(50). The ratio is bounded by "
                        + "6*exp(50)*log(X)/X^(1/4), which tends to zero. The integer five "
                        + "also witnesses strict positivity of the denominator "
                        + "for X at least five."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mccormack-zelinsky-2023-question-44"),
                    ResolutionKind.Proved)))));
}
