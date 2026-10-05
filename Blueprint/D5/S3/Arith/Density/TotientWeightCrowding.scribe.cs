using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class TotientWeightCrowdingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Density/TotientWeightCrowding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total Euler totient weight bounds the cardinality of every finite positive support.",
        H("Finite Totient Weight Crowding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-totient-weight-crowding"),
                DeclarationHandle.Create(Prefix + "finite_totient_weight_crowding"),
                H("A universal finite support estimate"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A be a finite set of positive natural numbers. "
                        + "Write k for its cardinality and W for the sum of the actual "
                        + "Euler totients of its members. Then k cubed is at most "
                        + "sixteen times W squared. All sums, products, and powers in "
                        + "the statement are natural-number operations. The empty set "
                        + "has k=W=0. No divisor closure or restriction on the largest "
                        + "member is required.")),
                    Paragraph(Text("Euler's classical product formula gives "
                        + "n <= 2 phi(n)^2 for every positive n. Indeed, write n=qR, "
                        + "where R is the product of its distinct prime factors, and "
                        + "put T equal to the product of p-1 over those factors. "
                        + "Then phi(n)=qT and q>=1. Every odd prime satisfies "
                        + "p <= (p-1)^2; the prime two contributes only a factor "
                        + "of two. Thus R<=2T^2 and n<=2(qT)^2.")),
                    Paragraph(Text("When k>0, split A into a low part satisfying "
                        + "4 phi(d)^2 <= k and its complement. Each low member "
                        + "lies between one and floor(k/2), so the low part has at "
                        + "most floor(k/2) members. If h is the size of the high "
                        + "part, then k<=2h and h>0.")),
                    Paragraph(Text("Let m be the minimum actual totient among "
                        + "the high members. Its minimizing member satisfies "
                        + "k<4m^2, and summing the lower bound m over the high "
                        + "part gives hm<=W. Consequently "
                        + "k^3 <= 4h^2 k <= 16(hm)^2 <= 16W^2. "
                        + "This estimate uses only positivity and distinctness of "
                        + "the indices."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var a = F.Id("A");
        var d = F.Id("d");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula positive = Seq(Forall, Sp, d, InMacro, Sp, a, Comma, D(0), Lt, d);
        Formula weight = Seq(new Formula.Subscript(Sum, Seq(d, InMacro, Sp, a)),
            Call("phi", d));
        Formula estimate = Seq(new Formula.Power(Call("card", a), D(3)), Le,
            D(1, 6), Cdot, new Formula.Power(Seq(Open, weight, Close), D(2)));
        return Disp(Seq(Forall, Sp, a, Colon, Sp, Call("Finset", naturals), Comma,
            Open, positive, Close, Rightarrow, estimate));
    }
}
